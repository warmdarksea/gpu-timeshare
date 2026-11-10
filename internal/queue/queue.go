// Package queue holds the requests not yet answered and the answers
// already given.
//
// A request is queued once, answered once, and deleted once its answer is
// delivered (a single request) or written to its batch's output (a batch
// line). Before anything is queued the cache is asked: the key is the
// question -- endpoint, the model's identity, the body as canonical JSON --
// so the same question costs the card nothing the second time, whoever
// asks it.
package queue

import (
	"bytes"
	"crypto/sha256"
	"database/sql"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"time"
)

// Canonical re-encodes JSON with sorted keys and no insignificant
// whitespace; numbers keep their literal spelling.
func Canonical(body []byte) ([]byte, error) {
	if c, err := fastCanonical(body); err == nil {
		return c, nil
	}
	return slowCanonical(body)
}

func slowCanonical(body []byte) ([]byte, error) {
	d := json.NewDecoder(bytes.NewReader(body))
	d.UseNumber()
	var v any
	if err := d.Decode(&v); err != nil {
		return nil, err
	}
	if d.More() {
		return nil, errors.New("trailing data after the JSON value")
	}
	var buf bytes.Buffer
	e := json.NewEncoder(&buf)
	e.SetEscapeHTML(false)
	if err := e.Encode(v); err != nil {
		return nil, err
	}
	return bytes.TrimRight(buf.Bytes(), "\n"), nil
}

// Key is the cache key of a question.
func Key(endpoint, identity string, body []byte) (string, error) {
	c, err := Canonical(body)
	if err != nil {
		return "", err
	}
	h := sha256.New()
	fmt.Fprintf(h, "gpu-timeshare/1\x00%s\x00%s\x00", endpoint, identity)
	h.Write(c)
	return hex.EncodeToString(h.Sum(nil)), nil
}

// Request is one queued request, as the scheduler sees it.
type Request struct {
	ID       int64
	BatchID  string // "" for a single request
	Client   string
	Model    string
	Endpoint string
	Key      string
	Attempts int
	Write    bool // cache the answer
}

type Queue struct {
	DB       *sql.DB
	FilesDir string
}

// Remember caches an answer.
func (q *Queue) Remember(key, model, identity, endpoint string, body []byte, elapsed time.Duration) error {
	now := time.Now().Unix()
	_, err := q.DB.Exec(`INSERT INTO cache(key, model, identity, endpoint, body, bytes, elapsed_ms, created, last_hit)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
		ON CONFLICT(key) DO UPDATE SET body = excluded.body, bytes = excluded.bytes,
		  elapsed_ms = excluded.elapsed_ms, created = excluded.created, last_hit = excluded.last_hit`,
		key, model, identity, endpoint, body, len(body), elapsed.Milliseconds(), now, now)
	return err
}

// New is a request to enqueue.
type New struct {
	BatchID      string
	Line         int
	CustomID     string
	Client       string
	Model        string
	Endpoint     string
	Body         []byte // a single request's
	FileID       string // a batch line's
	Off, Len     int64
	Key          string
	ReadCache    bool
	Write        bool
	MaxAge       time.Duration // > 0: the oldest cached answer acceptable
	OnlyIfCached bool          // no answer in the cache: failed (not_cached), never queued
}

// Insert queues a request -- or, when the cache already has its answer,
// records it as done from the cache. Returns its id and whether it was a
// hit. tx may be a transaction (a batch's lines go in one).
func (q *Queue) Insert(tx interface {
	Exec(string, ...any) (sql.Result, error)
	QueryRow(string, ...any) *sql.Row
}, n New) (int64, bool, error) {
	var cached []byte
	var cachedAt any
	if n.ReadCache {
		oldest := int64(0)
		if n.MaxAge > 0 {
			oldest = time.Now().Add(-n.MaxAge).Unix()
		}
		var at int64
		err := tx.QueryRow("SELECT body, created FROM cache WHERE key = ? AND created >= ?", n.Key, oldest).Scan(&cached, &at)
		if err == nil {
			cachedAt = at
		}
		if err != nil && !errors.Is(err, sql.ErrNoRows) {
			return 0, false, err
		}
		if cached != nil {
			if _, err := tx.Exec("UPDATE cache SET last_hit = ?, hits = hits + 1 WHERE key = ?",
				time.Now().Unix(), n.Key); err != nil {
				return 0, false, err
			}
		}
	}
	state, status, code, msg := "queued", any(nil), any(nil), any(nil)
	if cached != nil {
		state, status = "done", 200
	} else if n.OnlyIfCached {
		state, code, msg = "failed", "not_cached", "only-if-cached: no answer to this question is in the cache"
	}
	var batch, custom, fileID any
	if n.BatchID != "" {
		batch, custom, fileID = n.BatchID, n.CustomID, n.FileID
	}
	r, err := tx.Exec(`INSERT INTO requests(batch_id, line, custom_id, client, model, endpoint, body, file_id, off, len,
		cache_key, read_cache, write_cache, state, status_code, response, cached, cached_at, error_code, error, created)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
		batch, n.Line, custom, n.Client, n.Model, n.Endpoint, n.Body, fileID, n.Off, n.Len,
		n.Key, n.ReadCache, n.Write, state, status, cached, cached != nil, cachedAt, code, msg, time.Now().Unix())
	if err != nil {
		return 0, false, err
	}
	id, _ := r.LastInsertId()
	return id, cached != nil, nil
}

// Counts is how many requests each model has queued.
func (q *Queue) Counts() (map[string]int, error) {
	rows, err := q.DB.Query("SELECT model, COUNT(*) FROM requests WHERE state = 'queued' GROUP BY model")
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	out := map[string]int{}
	for rows.Next() {
		var m string
		var n int
		if err := rows.Scan(&m, &n); err != nil {
			return nil, err
		}
		out[m] = n
	}
	return out, rows.Err()
}

// Flow is one client's queued requests for one model (the ones being
// answered included: they stay queued until they are done).
type Flow struct {
	Client, Model string
	Queued        int
	Oldest        int64 // the id of its oldest
}

// Flows is what is queued, by model and client, in that order.
func (q *Queue) Flows() ([]Flow, error) {
	rows, err := q.DB.Query(`SELECT model, client, COUNT(*), MIN(id) FROM requests WHERE state = 'queued'
		GROUP BY model, client ORDER BY model, client`)
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	var out []Flow
	for rows.Next() {
		var f Flow
		if err := rows.Scan(&f.Model, &f.Client, &f.Queued, &f.Oldest); err != nil {
			return nil, err
		}
		out = append(out, f)
	}
	return out, rows.Err()
}

// Queued returns up to limit of a model's queued requests per client,
// each client's oldest first, single requests (someone is waiting) before
// batch lines.
func (q *Queue) Queued(model string, limit int) (map[string][]Request, error) {
	rows, err := q.DB.Query(`SELECT id, COALESCE(batch_id, ''), client, endpoint, cache_key, attempts, write_cache FROM (
		  SELECT *, ROW_NUMBER() OVER (PARTITION BY client ORDER BY batch_id IS NOT NULL, id) AS n
		  FROM requests WHERE state = 'queued' AND model = ?)
		WHERE n <= ? ORDER BY client, n`, model, limit)
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	out := map[string][]Request{}
	for rows.Next() {
		r := Request{Model: model}
		if err := rows.Scan(&r.ID, &r.BatchID, &r.Client, &r.Endpoint, &r.Key, &r.Attempts, &r.Write); err != nil {
			return nil, err
		}
		out[r.Client] = append(out[r.Client], r)
	}
	return out, rows.Err()
}

// Body is what a request sends upstream.
func (q *Queue) Body(id int64) ([]byte, error) {
	var body []byte
	var fileID sql.NullString
	var off, n sql.NullInt64
	err := q.DB.QueryRow("SELECT body, file_id, off, len FROM requests WHERE id = ?", id).Scan(&body, &fileID, &off, &n)
	if err != nil {
		return nil, err
	}
	if !fileID.Valid {
		return body, nil
	}
	f, err := os.Open(FilePath(q.FilesDir, fileID.String))
	if err != nil {
		return nil, err
	}
	defer f.Close()
	line := make([]byte, n.Int64)
	if _, err := f.ReadAt(line, off.Int64); err != nil {
		return nil, err
	}
	var l struct {
		Body json.RawMessage `json:"body"`
	}
	if err := json.Unmarshal(line, &l); err != nil {
		return nil, err
	}
	return l.Body, nil
}

func FilePath(dir, id string) string { return dir + string(os.PathSeparator) + id }

// Done records an answer. Others queued with the same key and willing to
// read the cache are answered with it too (returned, so their waiters can
// be woken).
func (q *Queue) Done(id int64, status int, reply []byte, key string, shareWithQueued bool) ([]int64, error) {
	tx, err := q.DB.Begin()
	if err != nil {
		return nil, err
	}
	defer tx.Rollback()
	if _, err := tx.Exec("UPDATE requests SET state = 'done', status_code = ?, response = ? WHERE id = ?",
		status, reply, id); err != nil {
		return nil, err
	}
	var also []int64
	if shareWithQueued {
		rows, err := tx.Query("SELECT id FROM requests WHERE state = 'queued' AND cache_key = ? AND read_cache", key)
		if err != nil {
			return nil, err
		}
		for rows.Next() {
			var o int64
			rows.Scan(&o)
			also = append(also, o)
		}
		rows.Close()
		for _, o := range also {
			if _, err := tx.Exec(`UPDATE requests SET state = 'done', status_code = ?, response = ?, cached = 1
				WHERE id = ?`, status, reply, o); err != nil {
				return nil, err
			}
		}
	}
	return also, tx.Commit()
}

// Retry puts a request back in the queue after a failed attempt -- or,
// once it has had max attempts, fails it.
func (q *Queue) Retry(id int64, msg string, max int) (failed bool, err error) {
	var attempts int
	if err := q.DB.QueryRow("UPDATE requests SET attempts = attempts + 1, error = ? WHERE id = ? RETURNING attempts",
		msg, id).Scan(&attempts); err != nil {
		return false, err
	}
	if attempts < max {
		return false, nil
	}
	return true, q.Fail(id, "model_error", fmt.Sprintf("%s (after %d attempts)", msg, attempts))
}

// Fail ends a request without an answer.
func (q *Queue) Fail(id int64, code, msg string) error {
	_, err := q.DB.Exec("UPDATE requests SET state = 'failed', error_code = ?, error = ? WHERE id = ?", code, msg, id)
	return err
}

// FailQueued fails every queued request for a model; returns their ids.
func (q *Queue) FailQueued(model, code, msg string) ([]int64, error) {
	rows, err := q.DB.Query(`UPDATE requests SET state = 'failed', error_code = ?, error = ?
		WHERE state = 'queued' AND model = ? RETURNING id`, code, msg, model)
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	var ids []int64
	for rows.Next() {
		var id int64
		rows.Scan(&id)
		ids = append(ids, id)
	}
	return ids, rows.Err()
}

// Result is a finished request.
type Result struct {
	State     string // done | failed | queued
	Status    int
	Body      []byte
	ErrorCode string
	Error     string
	Cached    bool
	CachedAt  int64 // when the cached answer was made; 0 for a twin's answer or none
}

func (q *Queue) Result(id int64) (Result, error) {
	var r Result
	var status, at sql.NullInt64
	var code, msg sql.NullString
	err := q.DB.QueryRow("SELECT state, status_code, response, error_code, error, cached, cached_at FROM requests WHERE id = ?", id).
		Scan(&r.State, &status, &r.Body, &code, &msg, &r.Cached, &at)
	r.Status, r.ErrorCode, r.Error, r.CachedAt = int(status.Int64), code.String, msg.String, at.Int64
	return r, err
}

// Forget deletes a request (its answer delivered, or nobody waiting).
func (q *Queue) Forget(id int64) error {
	_, err := q.DB.Exec("DELETE FROM requests WHERE id = ?", id)
	return err
}

// ForgetSingles deletes the single requests left by a previous run: their
// callers' connections died with it.
func (q *Queue) ForgetSingles() (int64, error) {
	r, err := q.DB.Exec("DELETE FROM requests WHERE batch_id IS NULL")
	if err != nil {
		return 0, err
	}
	return r.RowsAffected()
}

// ---- the cache's upkeep ----------------------------------------------------

// Expiry is the cache's limits; zero means none.
type Expiry struct {
	MaxAge    time.Duration
	MaxUnused time.Duration
	MaxSize   int64
}

// Expire drops answers past the limits and returns how many went.
func (q *Queue) Expire(e Expiry, now time.Time) (int64, error) {
	var n int64
	del := func(query string, args ...any) error {
		r, err := q.DB.Exec(query, args...)
		if err != nil {
			return err
		}
		k, _ := r.RowsAffected()
		n += k
		return nil
	}
	if e.MaxAge > 0 {
		if err := del("DELETE FROM cache WHERE created < ?", now.Add(-e.MaxAge).Unix()); err != nil {
			return n, err
		}
	}
	if e.MaxUnused > 0 {
		if err := del("DELETE FROM cache WHERE last_hit < ?", now.Add(-e.MaxUnused).Unix()); err != nil {
			return n, err
		}
	}
	if e.MaxSize > 0 {
		// least recently used first, until what's left fits
		if err := del(`DELETE FROM cache WHERE key IN (
			  SELECT key FROM (
			    SELECT key, SUM(bytes) OVER (ORDER BY last_hit DESC, created DESC, key) AS kept FROM cache)
			  WHERE kept > ?)`, e.MaxSize); err != nil {
			return n, err
		}
	}
	return n, nil
}

// Stats is the cache per model.
type Stats struct {
	Model    string
	Identity string
	Answers  int64
	Bytes    int64
	Hits     int64
	MeanMs   float64
}

func (q *Queue) Stats() ([]Stats, error) {
	rows, err := q.DB.Query(`SELECT model, identity, COUNT(*), SUM(bytes), SUM(hits), AVG(elapsed_ms)
		FROM cache GROUP BY model, identity ORDER BY model, identity`)
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	var out []Stats
	for rows.Next() {
		var s Stats
		if err := rows.Scan(&s.Model, &s.Identity, &s.Answers, &s.Bytes, &s.Hits, &s.MeanMs); err != nil {
			return nil, err
		}
		out = append(out, s)
	}
	return out, rows.Err()
}

// Clear drops cached answers: one model's, or all of them.
func (q *Queue) Clear(model string) (int64, error) {
	var r sql.Result
	var err error
	if model == "" {
		r, err = q.DB.Exec("DELETE FROM cache")
	} else {
		r, err = q.DB.Exec("DELETE FROM cache WHERE model = ?", model)
	}
	if err != nil {
		return 0, err
	}
	return r.RowsAffected()
}
