// Package batch is the OpenAI Files and Batch APIs' state: uploaded files,
// batches made from them, and the result files written when a batch ends.
//
// A batch's lines are queued as requests (package queue) when it is made;
// it is finished when none of them is queued or running. Then its output
// file (the answers) and error file (the lines that got none) are written,
// in input order, and its requests are deleted.
//
// Beyond OpenAI's rules, and only where that costs a client nothing: a
// batch may mix models, and its completion window may be any duration up
// to [limits].max_window. A file valid for OpenAI is valid here.
package batch

import (
	"bufio"
	"crypto/rand"
	"database/sql"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"time"

	"gpu-timeshare/internal/config"
	"gpu-timeshare/internal/queue"
)

func newID(prefix string) string {
	b := make([]byte, 12)
	rand.Read(b)
	return prefix + hex.EncodeToString(b)
}

// File is an OpenAI file object.
type File struct {
	ID        string `json:"id"`
	Object    string `json:"object"`
	Bytes     int64  `json:"bytes"`
	CreatedAt int64  `json:"created_at"`
	Filename  string `json:"filename"`
	Purpose   string `json:"purpose"`
	Status    string `json:"status"`
	Client    string `json:"-"`
}

type Store struct {
	DB  *sql.DB
	Cfg *config.Config
	Q   *queue.Queue
}

var ErrNotFound = errors.New("not found")
var ErrInUse = errors.New("in use by a batch that has not finished")

// SaveFile stores an upload, refusing one past the size limit.
func (s *Store) SaveFile(client, purpose, filename string, r io.Reader) (File, error) {
	f := File{ID: newID("file-"), Object: "file", CreatedAt: time.Now().Unix(), Filename: filename,
		Purpose: purpose, Status: "processed", Client: client}
	path := queue.FilePath(s.Cfg.FilesDir(), f.ID)
	out, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o640)
	if err != nil {
		return f, err
	}
	limit := int64(s.Cfg.Limits.MaxFile)
	if limit <= 0 {
		limit = 1 << 62
	}
	n, err := io.Copy(out, io.LimitReader(r, limit+1))
	if cerr := out.Close(); err == nil {
		err = cerr
	}
	if err == nil && n > limit {
		err = fmt.Errorf("the file is over the %d-byte limit", limit)
	}
	if err != nil {
		os.Remove(path)
		return f, err
	}
	f.Bytes = n
	_, err = s.DB.Exec("INSERT INTO files(id, client, purpose, filename, bytes, created_at) VALUES (?, ?, ?, ?, ?, ?)",
		f.ID, client, purpose, filename, n, f.CreatedAt)
	if err != nil {
		os.Remove(path)
	}
	return f, err
}

// GetFile finds a file this client may see (an admin sees every file).
func (s *Store) GetFile(id, client string, admin bool) (File, error) {
	f := File{Object: "file", Status: "processed"}
	err := s.DB.QueryRow("SELECT id, client, purpose, filename, bytes, created_at FROM files WHERE id = ?", id).
		Scan(&f.ID, &f.Client, &f.Purpose, &f.Filename, &f.Bytes, &f.CreatedAt)
	if errors.Is(err, sql.ErrNoRows) || (err == nil && !admin && f.Client != client) {
		return f, ErrNotFound
	}
	return f, err
}

func (s *Store) ListFiles(client string, admin bool, purpose string) ([]File, error) {
	rows, err := s.DB.Query(`SELECT id, client, purpose, filename, bytes, created_at FROM files
		WHERE (? OR client = ?) AND (? = '' OR purpose = ?) ORDER BY created_at DESC, id`, admin, client, purpose, purpose)
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	var out []File
	for rows.Next() {
		f := File{Object: "file", Status: "processed"}
		if err := rows.Scan(&f.ID, &f.Client, &f.Purpose, &f.Filename, &f.Bytes, &f.CreatedAt); err != nil {
			return nil, err
		}
		out = append(out, f)
	}
	return out, rows.Err()
}

// DeleteFile removes a file, unless a batch still reading it hasn't ended.
func (s *Store) DeleteFile(id, client string, admin bool) error {
	if _, err := s.GetFile(id, client, admin); err != nil {
		return err
	}
	var n int
	s.DB.QueryRow("SELECT COUNT(*) FROM requests WHERE file_id = ?", id).Scan(&n)
	if n > 0 {
		return ErrInUse
	}
	if _, err := s.DB.Exec("DELETE FROM files WHERE id = ?", id); err != nil {
		return err
	}
	os.Remove(queue.FilePath(s.Cfg.FilesDir(), id))
	return nil
}

// ExpireFiles deletes files past the retention period, except those a
// batch still reads.
func (s *Store) ExpireFiles(now time.Time) (int, error) {
	keep := s.Cfg.Limits.FileRetention.Duration
	if keep <= 0 {
		return 0, nil
	}
	rows, err := s.DB.Query(`SELECT id FROM files WHERE created_at < ?
		AND id NOT IN (SELECT DISTINCT file_id FROM requests WHERE file_id IS NOT NULL)`, now.Add(-keep).Unix())
	if err != nil {
		return 0, err
	}
	var ids []string
	for rows.Next() {
		var id string
		rows.Scan(&id)
		ids = append(ids, id)
	}
	rows.Close()
	for _, id := range ids {
		s.DB.Exec("DELETE FROM files WHERE id = ?", id)
		os.Remove(queue.FilePath(s.Cfg.FilesDir(), id))
	}
	return len(ids), nil
}

// ---- batches ---------------------------------------------------------------

// Batch is an OpenAI batch object.
type Batch struct {
	ID               string          `json:"id"`
	Object           string          `json:"object"`
	Endpoint         string          `json:"endpoint"`
	Errors           json.RawMessage `json:"errors"`
	InputFileID      string          `json:"input_file_id"`
	CompletionWindow string          `json:"completion_window"`
	Status           string          `json:"status"`
	OutputFileID     *string         `json:"output_file_id"`
	ErrorFileID      *string         `json:"error_file_id"`
	CreatedAt        int64           `json:"created_at"`
	InProgressAt     *int64          `json:"in_progress_at"`
	ExpiresAt        *int64          `json:"expires_at"`
	FinalizingAt     *int64          `json:"finalizing_at"`
	CompletedAt      *int64          `json:"completed_at"`
	FailedAt         *int64          `json:"failed_at"`
	ExpiredAt        *int64          `json:"expired_at"`
	CancellingAt     *int64          `json:"cancelling_at"`
	CancelledAt      *int64          `json:"cancelled_at"`
	RequestCounts    Counts          `json:"request_counts"`
	Metadata         json.RawMessage `json:"metadata"`
	Client           string          `json:"-"`
}

type Counts struct {
	Total     int `json:"total"`
	Completed int `json:"completed"`
	Failed    int `json:"failed"`
}

// LineError is one entry of a batch's errors (why it failed validation).
type LineError struct {
	Code    string `json:"code"`
	Message string `json:"message"`
	Param   string `json:"param,omitempty"`
	Line    *int   `json:"line,omitempty"`
}

func errorList(errs []LineError) json.RawMessage {
	b, _ := json.Marshal(map[string]any{"object": "list", "data": errs})
	return b
}

// Create is POST /v1/batches.
type Create struct {
	InputFileID      string          `json:"input_file_id"`
	Endpoint         string          `json:"endpoint"`
	CompletionWindow string          `json:"completion_window"`
	Metadata         json.RawMessage `json:"metadata"`
}

// BadRequest is a create that can't be a batch at all (the caller's error).
type BadRequest struct{ Msg, Param string }

func (e *BadRequest) Error() string { return e.Msg }

// line is one line of a batch input file.
type line struct {
	CustomID string          `json:"custom_id"`
	Method   string          `json:"method"`
	URL      string          `json:"url"`
	Body     json.RawMessage `json:"body"`
}

// New makes a batch: checks the file line by line and queues every line.
// A file that fails the checks makes a batch that has failed, with the
// reasons in its errors, as OpenAI does; nothing of it is queued.
// Returns the batch and the number of lines already answered by the cache.
// pol is the create request's Cache-Control, for every line (each line also
// needs its model to cache).
func (s *Store) New(client string, admin bool, c Create, pol queue.Policy) (Batch, int, error) {
	if c.InputFileID == "" {
		return Batch{}, 0, &BadRequest{"input_file_id is required", "input_file_id"}
	}
	if !s.Cfg.Allows(c.Endpoint) {
		return Batch{}, 0, &BadRequest{fmt.Sprintf("endpoint %q is not served here", c.Endpoint), "endpoint"}
	}
	window, err := parseWindow(c.CompletionWindow)
	if err != nil || window <= 0 {
		return Batch{}, 0, &BadRequest{fmt.Sprintf("completion_window %q: want a duration such as 24h", c.CompletionWindow), "completion_window"}
	}
	if max := s.Cfg.Limits.MaxWindow.Duration; max > 0 && window > max {
		return Batch{}, 0, &BadRequest{fmt.Sprintf("completion_window %q is over the %s limit", c.CompletionWindow, max), "completion_window"}
	}
	if len(c.Metadata) == 0 || string(c.Metadata) == "null" {
		c.Metadata = json.RawMessage("null")
	} else {
		var m map[string]string
		if json.Unmarshal(c.Metadata, &m) != nil {
			return Batch{}, 0, &BadRequest{"metadata: want an object of strings", "metadata"}
		}
	}
	f, err := s.GetFile(c.InputFileID, client, admin)
	if errors.Is(err, ErrNotFound) {
		return Batch{}, 0, &BadRequest{fmt.Sprintf("no file %q", c.InputFileID), "input_file_id"}
	}
	if err != nil {
		return Batch{}, 0, err
	}
	if f.Purpose != "batch" {
		return Batch{}, 0, &BadRequest{fmt.Sprintf("file %s has purpose %q, not \"batch\"", f.ID, f.Purpose), "input_file_id"}
	}

	now := time.Now().Unix()
	b := Batch{ID: newID("batch_"), Object: "batch", Endpoint: c.Endpoint, InputFileID: f.ID,
		CompletionWindow: c.CompletionWindow, CreatedAt: now, Metadata: c.Metadata, Client: client}
	lines, errs, err := s.read(f, c.Endpoint)
	if err != nil {
		return b, 0, err
	}
	if len(errs) > 0 {
		b.Status, b.FailedAt, b.Errors = "failed", &now, errorList(errs)
		_, err := s.DB.Exec(`INSERT INTO batches(id, client, endpoint, input_file_id, completion_window, status,
			errors, metadata, created_at, failed_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
			b.ID, client, b.Endpoint, f.ID, b.CompletionWindow, b.Status, string(b.Errors), string(b.Metadata), now, now)
		return b, 0, err
	}

	expires := now + int64(window/time.Second)
	b.Status, b.InProgressAt, b.ExpiresAt = "in_progress", &now, &expires
	b.RequestCounts.Total = len(lines)
	tx, err := s.DB.Begin()
	if err != nil {
		return b, 0, err
	}
	defer tx.Rollback()
	if _, err := tx.Exec(`INSERT INTO batches(id, client, endpoint, input_file_id, completion_window, status,
		metadata, no_cache, created_at, in_progress_at, expires_at, total) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,
		b.ID, client, b.Endpoint, f.ID, b.CompletionWindow, b.Status, string(b.Metadata), !pol.Read,
		now, now, expires, len(lines)); err != nil {
		return b, 0, err
	}
	hits := 0
	for i, l := range lines {
		n := queue.New{BatchID: b.ID, Line: i, CustomID: l.CustomID, Client: client, Model: l.model,
			Endpoint: c.Endpoint, FileID: f.ID, Off: l.off, Len: l.len, Key: l.key}
		if l.unknown {
			// a model this server doesn't have: answered at once, with an error
			n.Key = "unknown-model"
			id, _, err := s.Q.Insert(tx, n)
			if err != nil {
				return b, 0, err
			}
			if _, err := tx.Exec("UPDATE requests SET state = 'failed', error_code = 'model_not_found', error = ? WHERE id = ?",
				fmt.Sprintf("no model %q here", l.model), id); err != nil {
				return b, 0, err
			}
			continue
		}
		n.ReadCache, n.Write = pol.Read && l.caches, pol.Write && l.caches
		n.MaxAge, n.OnlyIfCached = pol.MaxAge, pol.OnlyIfCached
		_, hit, err := s.Q.Insert(tx, n)
		if err != nil {
			return b, 0, err
		}
		if hit {
			hits++
		}
	}
	return b, hits, tx.Commit()
}

func parseWindow(s string) (time.Duration, error) {
	var d config.Duration
	err := d.UnmarshalText([]byte(s))
	return d.Duration, err
}

type parsed struct {
	CustomID string
	model    string
	key      string
	off, len int64
	unknown  bool
	caches   bool
}

// read checks every line of an input file; the errors are the batch's.
func (s *Store) read(f File, endpoint string) ([]parsed, []LineError, error) {
	fh, err := os.Open(queue.FilePath(s.Cfg.FilesDir(), f.ID))
	if err != nil {
		return nil, nil, err
	}
	defer fh.Close()
	r := bufio.NewReaderSize(fh, 1<<20)
	var out []parsed
	var errs []LineError
	seen := map[string]bool{}
	bad := func(n int, code, msg, param string) {
		if len(errs) < 100 {
			ln := n
			errs = append(errs, LineError{Code: code, Message: msg, Param: param, Line: &ln})
		}
	}
	var off int64
	maxBody := int64(s.Cfg.Limits.MaxBody)
	for n := 1; ; n++ {
		raw, err := r.ReadBytes('\n')
		if len(raw) == 0 && err == io.EOF {
			break
		}
		if err != nil && err != io.EOF {
			return nil, nil, err
		}
		start, length := off, int64(len(raw))
		off += length
		trimmed := trimSpace(raw)
		if len(trimmed) == 0 {
			continue
		}
		if s.Cfg.Limits.MaxBatchLines > 0 && len(out) >= s.Cfg.Limits.MaxBatchLines {
			bad(n, "too_many_requests", fmt.Sprintf("a batch holds at most %d requests", s.Cfg.Limits.MaxBatchLines), "")
			break
		}
		var l line
		if err := json.Unmarshal(trimmed, &l); err != nil {
			bad(n, "invalid_json_line", "not a JSON object: "+err.Error(), "")
			continue
		}
		switch {
		case l.CustomID == "":
			bad(n, "missing_required_parameter", "custom_id is required", "custom_id")
			continue
		case seen[l.CustomID]:
			bad(n, "duplicate_custom_id", fmt.Sprintf("custom_id %q appears twice", l.CustomID), "custom_id")
			continue
		case l.Method != "POST":
			bad(n, "invalid_request", "method must be POST", "method")
			continue
		case l.URL != endpoint:
			bad(n, "mismatched_endpoint", fmt.Sprintf("url %q is not the batch's endpoint %q", l.URL, endpoint), "url")
			continue
		case len(l.Body) == 0 || l.Body[0] != '{':
			bad(n, "invalid_request", "body must be a JSON object", "body")
			continue
		case maxBody > 0 && int64(len(l.Body)) > maxBody:
			bad(n, "request_too_large", fmt.Sprintf("body is over the %d-byte limit", maxBody), "body")
			continue
		}
		seen[l.CustomID] = true
		var head struct {
			Model  string `json:"model"`
			Stream bool   `json:"stream"`
		}
		json.Unmarshal(l.Body, &head)
		if head.Model == "" {
			bad(n, "missing_required_parameter", "body.model is required", "body.model")
			continue
		}
		if head.Stream {
			bad(n, "invalid_request", "stream is not available in a batch", "body.stream")
			continue
		}
		p := parsed{CustomID: l.CustomID, model: head.Model, off: start, len: length}
		m, ok := s.Cfg.Models[head.Model]
		if !ok {
			p.unknown = true
		} else {
			p.caches = m.Caches(s.Cfg)
			p.key, err = queue.Key(endpoint, m.Identity(), l.Body)
			if err != nil {
				bad(n, "invalid_json_line", "body: "+err.Error(), "body")
				continue
			}
		}
		out = append(out, p)
	}
	if len(out) == 0 && len(errs) == 0 {
		errs = append(errs, LineError{Code: "empty_file", Message: "the input file has no requests"})
	}
	return out, errs, nil
}

func trimSpace(b []byte) []byte {
	for len(b) > 0 && (b[len(b)-1] == '\n' || b[len(b)-1] == '\r' || b[len(b)-1] == ' ' || b[len(b)-1] == '\t') {
		b = b[:len(b)-1]
	}
	for len(b) > 0 && (b[0] == ' ' || b[0] == '\t') {
		b = b[1:]
	}
	return b
}

const batchCols = `id, client, endpoint, input_file_id, completion_window, status, output_file_id, error_file_id,
	errors, metadata, created_at, in_progress_at, expires_at, finalizing_at, completed_at, failed_at, expired_at,
	cancelling_at, cancelled_at, total, completed, failed`

func scanBatch(row interface{ Scan(...any) error }) (Batch, error) {
	b := Batch{Object: "batch"}
	var out, errf, errs, meta sql.NullString
	var ts [8]sql.NullInt64
	err := row.Scan(&b.ID, &b.Client, &b.Endpoint, &b.InputFileID, &b.CompletionWindow, &b.Status, &out, &errf,
		&errs, &meta, &b.CreatedAt, &ts[0], &ts[1], &ts[2], &ts[3], &ts[4], &ts[5], &ts[6], &ts[7],
		&b.RequestCounts.Total, &b.RequestCounts.Completed, &b.RequestCounts.Failed)
	if err != nil {
		return b, err
	}
	if b.Status == "expiring" { // ours: expired, its files not yet written
		b.Status = "finalizing"
	}
	if out.Valid {
		b.OutputFileID = &out.String
	}
	if errf.Valid {
		b.ErrorFileID = &errf.String
	}
	b.Errors = json.RawMessage("null")
	if errs.Valid {
		b.Errors = json.RawMessage(errs.String)
	}
	b.Metadata = json.RawMessage("null")
	if meta.Valid && meta.String != "" {
		b.Metadata = json.RawMessage(meta.String)
	}
	ptr := func(n sql.NullInt64) *int64 {
		if !n.Valid {
			return nil
		}
		v := n.Int64
		return &v
	}
	b.InProgressAt, b.ExpiresAt, b.FinalizingAt, b.CompletedAt = ptr(ts[0]), ptr(ts[1]), ptr(ts[2]), ptr(ts[3])
	b.FailedAt, b.ExpiredAt, b.CancellingAt, b.CancelledAt = ptr(ts[4]), ptr(ts[5]), ptr(ts[6]), ptr(ts[7])
	return b, nil
}

// Get finds a batch this client may see, with live counts while it runs.
func (s *Store) Get(id, client string, admin bool) (Batch, error) {
	b, err := scanBatch(s.DB.QueryRow("SELECT "+batchCols+" FROM batches WHERE id = ?", id))
	if errors.Is(err, sql.ErrNoRows) || (err == nil && !admin && b.Client != client) {
		return b, ErrNotFound
	}
	if err != nil {
		return b, err
	}
	return b, s.live(&b)
}

func (s *Store) live(b *Batch) error {
	if b.Status != "in_progress" && b.Status != "cancelling" && b.Status != "finalizing" {
		return nil
	}
	return s.DB.QueryRow(`SELECT COALESCE(SUM(state = 'done'), 0), COALESCE(SUM(state = 'failed'), 0)
		FROM requests WHERE batch_id = ?`, b.ID).Scan(&b.RequestCounts.Completed, &b.RequestCounts.Failed)
}

// List is a client's batches, newest first, after the given id.
func (s *Store) List(client string, admin bool, after string, limit int) ([]Batch, bool, error) {
	if limit <= 0 || limit > 100 {
		limit = 20
	}
	q := "SELECT " + batchCols + " FROM batches WHERE (? OR client = ?)"
	args := []any{admin, client}
	if after != "" {
		q += " AND (created_at, id) < (SELECT created_at, id FROM batches WHERE id = ?)"
		args = append(args, after)
	}
	q += " ORDER BY created_at DESC, id DESC LIMIT ?"
	args = append(args, limit+1)
	rows, err := s.DB.Query(q, args...)
	if err != nil {
		return nil, false, err
	}
	var out []Batch
	for rows.Next() {
		b, err := scanBatch(rows)
		if err != nil {
			rows.Close()
			return nil, false, err
		}
		out = append(out, b)
	}
	rows.Close()
	more := len(out) > limit
	if more {
		out = out[:limit]
	}
	for i := range out {
		if err := s.live(&out[i]); err != nil {
			return nil, false, err
		}
	}
	return out, more, nil
}

// Cancel stops a batch: what is queued fails as cancelled, what is running
// finishes, then the batch ends with what it has.
func (s *Store) Cancel(id, client string, admin bool) (Batch, error) {
	b, err := s.Get(id, client, admin)
	if err != nil {
		return b, err
	}
	if b.Status != "in_progress" && b.Status != "validating" {
		return b, nil // already ending or ended: cancelling is a no-op
	}
	now := time.Now().Unix()
	if _, err := s.DB.Exec("UPDATE batches SET status = 'cancelling', cancelling_at = ? WHERE id = ?", now, id); err != nil {
		return b, err
	}
	if _, err := s.DB.Exec(`UPDATE requests SET state = 'failed', error_code = 'batch_cancelled',
		error = 'the batch was cancelled' WHERE batch_id = ? AND state = 'queued'`, id); err != nil {
		return b, err
	}
	return s.Get(id, client, admin)
}

// Expire ends batches whose window has closed: their queued lines fail as
// expired. Returns the ids it expired.
func (s *Store) Expire(now time.Time) ([]string, error) {
	rows, err := s.DB.Query("SELECT id FROM batches WHERE status = 'in_progress' AND expires_at <= ?", now.Unix())
	if err != nil {
		return nil, err
	}
	var ids []string
	for rows.Next() {
		var id string
		rows.Scan(&id)
		ids = append(ids, id)
	}
	rows.Close()
	for _, id := range ids {
		if _, err := s.DB.Exec(`UPDATE requests SET state = 'failed', error_code = 'batch_expired',
			error = 'the batch expired before this request ran' WHERE batch_id = ? AND state = 'queued'`, id); err != nil {
			return nil, err
		}
		if _, err := s.DB.Exec("UPDATE batches SET status = 'expiring' WHERE id = ?", id); err != nil {
			return nil, err
		}
	}
	return ids, nil
}

// Finished are the batches with nothing queued that may be finalized, as
// far as the queue knows; running says whether any of a batch's requests
// is still in flight.
func (s *Store) Finished(running func(batchID string) bool) ([]string, error) {
	rows, err := s.DB.Query(`SELECT id FROM batches WHERE status IN ('in_progress', 'cancelling', 'expiring')
		AND NOT EXISTS (SELECT 1 FROM requests WHERE batch_id = batches.id AND state = 'queued')`)
	if err != nil {
		return nil, err
	}
	var ids []string
	for rows.Next() {
		var id string
		rows.Scan(&id)
		ids = append(ids, id)
	}
	rows.Close()
	var out []string
	for _, id := range ids {
		if !running(id) {
			out = append(out, id)
		}
	}
	return out, nil
}

// outLine is one line of an output or error file.
type outLine struct {
	ID       string    `json:"id"`
	CustomID string    `json:"custom_id"`
	Response *response `json:"response"`
	Error    *errBody  `json:"error"`
}

type response struct {
	StatusCode int             `json:"status_code"`
	RequestID  string          `json:"request_id"`
	Body       json.RawMessage `json:"body"`
	// ours: the Cache-Status a single request would have got
	CacheStatus string `json:"cache_status,omitempty"`
}

type errBody struct {
	Code    string `json:"code"`
	Message string `json:"message"`
}

// Finalize writes a batch's output and error files and deletes its
// requests. rewrite turns a stored answer into what the client sees.
func (s *Store) Finalize(id string, rewrite func(model string, body []byte) []byte) error {
	var status, client string
	if err := s.DB.QueryRow("SELECT status, client FROM batches WHERE id = ?", id).Scan(&status, &client); err != nil {
		return err
	}
	now := time.Now().Unix()
	s.DB.Exec("UPDATE batches SET finalizing_at = ? WHERE id = ?", now, id)

	type row struct {
		id              int64
		custom, state   string
		model           string
		statusCode      sql.NullInt64
		resp            []byte
		errCode, errMsg sql.NullString
		read, write     bool
		cached          bool
		cachedAt        sql.NullInt64
	}
	rows, err := s.DB.Query(`SELECT id, custom_id, state, model, status_code, response, error_code, error,
		read_cache, write_cache, cached, cached_at
		FROM requests WHERE batch_id = ? ORDER BY line`, id)
	if err != nil {
		return err
	}
	var all []row
	for rows.Next() {
		var r row
		if err := rows.Scan(&r.id, &r.custom, &r.state, &r.model, &r.statusCode, &r.resp, &r.errCode, &r.errMsg,
			&r.read, &r.write, &r.cached, &r.cachedAt); err != nil {
			rows.Close()
			return err
		}
		all = append(all, r)
	}
	rows.Close()

	outID, errID := newID("file-"), newID("file-")
	outF, err := os.Create(queue.FilePath(s.Cfg.FilesDir(), outID))
	if err != nil {
		return err
	}
	errF, err := os.Create(queue.FilePath(s.Cfg.FilesDir(), errID))
	if err != nil {
		outF.Close()
		return err
	}
	ow, ew := bufio.NewWriter(outF), bufio.NewWriter(errF)
	var nOut, nErr int
	for _, r := range all {
		l := outLine{ID: fmt.Sprintf("batch_req_%d", r.id), CustomID: r.custom}
		var w *bufio.Writer
		if r.state == "done" {
			body := r.resp
			if rewrite != nil {
				body = rewrite(r.model, body)
			}
			if !json.Valid(body) {
				b, _ := json.Marshal(string(body))
				body = b
			}
			status := queue.CacheStatus(queue.Policy{Read: r.read, Write: r.write},
				queue.Result{Status: int(r.statusCode.Int64), Cached: r.cached, CachedAt: r.cachedAt.Int64})
			l.Response = &response{StatusCode: int(r.statusCode.Int64), RequestID: fmt.Sprintf("req_%d", r.id), Body: body,
				CacheStatus: status}
			w = ow
			nOut++
		} else {
			code, msg := r.errCode.String, r.errMsg.String
			if r.state == "queued" { // can't happen after Finished; be safe
				code, msg = "batch_expired", "the request never ran"
			}
			l.Error = &errBody{Code: code, Message: msg}
			w = ew
			nErr++
		}
		b, _ := json.Marshal(l)
		w.Write(append(b, '\n'))
	}
	var werr error
	for _, f := range []struct {
		w *bufio.Writer
		f *os.File
	}{{ow, outF}, {ew, errF}} {
		if err := f.w.Flush(); err != nil && werr == nil {
			werr = err
		}
		if err := f.f.Close(); err != nil && werr == nil {
			werr = err
		}
	}
	if werr != nil {
		return werr
	}

	tx, err := s.DB.Begin()
	if err != nil {
		return err
	}
	defer tx.Rollback()
	var outCol, errCol any
	register := func(fid string, n int, name string) (any, error) {
		path := queue.FilePath(s.Cfg.FilesDir(), fid)
		if n == 0 {
			os.Remove(path)
			return nil, nil
		}
		st, err := os.Stat(path)
		if err != nil {
			return nil, err
		}
		_, err = tx.Exec("INSERT INTO files(id, client, purpose, filename, bytes, created_at) VALUES (?, ?, 'batch_output', ?, ?, ?)",
			fid, client, name, st.Size(), now)
		return fid, err
	}
	if outCol, err = register(outID, nOut, id+"_output.jsonl"); err != nil {
		return err
	}
	if errCol, err = register(errID, nErr, id+"_error.jsonl"); err != nil {
		return err
	}
	final, at := "completed", "completed_at"
	switch status {
	case "cancelling":
		final, at = "cancelled", "cancelled_at"
	case "expiring":
		final, at = "expired", "expired_at"
	}
	if _, err := tx.Exec(fmt.Sprintf(`UPDATE batches SET status = ?, %s = ?, output_file_id = ?, error_file_id = ?,
		completed = ?, failed = ? WHERE id = ?`, at), final, now, outCol, errCol, nOut, nErr, id); err != nil {
		return err
	}
	if _, err := tx.Exec("DELETE FROM requests WHERE batch_id = ?", id); err != nil {
		return err
	}
	return tx.Commit()
}
