// Package db is gpu-timeshare's state: clients, uploaded files, batches,
// the queue of requests not yet answered, and the answer cache. One
// sqlite file; the files' contents live beside it on disk.
package db

import (
	"database/sql"
	"path/filepath"

	_ "modernc.org/sqlite"
)

const schema = `
CREATE TABLE IF NOT EXISTS clients (
  name      TEXT    PRIMARY KEY,
  token_sha TEXT    NOT NULL UNIQUE,
  admin     INTEGER NOT NULL DEFAULT 0,
  created   INTEGER NOT NULL
);

-- uploads (purpose "batch") and the batches' results ("batch_output");
-- the bytes are in files/<id>
CREATE TABLE IF NOT EXISTS files (
  id         TEXT    PRIMARY KEY,
  client     TEXT    NOT NULL,
  purpose    TEXT    NOT NULL,
  filename   TEXT    NOT NULL,
  bytes      INTEGER NOT NULL,
  created_at INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS batches (
  id                TEXT    PRIMARY KEY,
  client            TEXT    NOT NULL,
  endpoint          TEXT    NOT NULL,
  input_file_id     TEXT    NOT NULL,
  completion_window TEXT    NOT NULL,
  status            TEXT    NOT NULL,
  output_file_id    TEXT,
  error_file_id     TEXT,
  errors            TEXT,   -- json: {"object": "list", "data": [...]}
  metadata          TEXT,   -- json object, the client's
  no_cache          INTEGER NOT NULL DEFAULT 0,
  created_at        INTEGER NOT NULL,
  in_progress_at    INTEGER,
  expires_at        INTEGER,
  finalizing_at     INTEGER,
  completed_at      INTEGER,
  failed_at         INTEGER,
  expired_at        INTEGER,
  cancelling_at     INTEGER,
  cancelled_at      INTEGER,
  total             INTEGER NOT NULL DEFAULT 0,
  completed         INTEGER NOT NULL DEFAULT 0,
  failed            INTEGER NOT NULL DEFAULT 0
);

-- every request not yet delivered: a single request until its caller has
-- the answer, a batch's lines until the batch's files are written. Only
-- outstanding work lives here.
CREATE TABLE IF NOT EXISTS requests (
  id          INTEGER PRIMARY KEY,
  batch_id    TEXT,               -- NULL: a single request, someone is waiting
  line        INTEGER,            -- its line in the batch's input file
  custom_id   TEXT,
  client      TEXT    NOT NULL,
  model       TEXT    NOT NULL,
  endpoint    TEXT    NOT NULL,
  body        BLOB,               -- a single request's body
  file_id     TEXT,               -- a batch line's: read from the input file
  off         INTEGER,
  len         INTEGER,
  cache_key   TEXT    NOT NULL,
  read_cache  INTEGER NOT NULL,
  write_cache INTEGER NOT NULL,
  state       TEXT    NOT NULL,   -- queued | done | failed
  attempts    INTEGER NOT NULL DEFAULT 0,
  status_code INTEGER,
  response    BLOB,
  error_code  TEXT,
  error       TEXT,
  cached      INTEGER NOT NULL DEFAULT 0,  -- answered by the cache, or by a twin in flight
  cached_at   INTEGER,                     -- the cached answer's time (NULL: a twin's)
  created     INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS requests_queued ON requests(model, client, id) WHERE state = 'queued';
CREATE INDEX IF NOT EXISTS requests_batch ON requests(batch_id, line);
CREATE INDEX IF NOT EXISTS requests_key ON requests(cache_key) WHERE state = 'queued';

-- answers, verbatim, by the question that produced them
CREATE TABLE IF NOT EXISTS cache (
  key         TEXT    PRIMARY KEY,
  model       TEXT    NOT NULL,
  identity    TEXT    NOT NULL,
  endpoint    TEXT    NOT NULL,
  body        BLOB    NOT NULL,
  bytes       INTEGER NOT NULL,
  elapsed_ms  INTEGER NOT NULL,
  created     INTEGER NOT NULL,
  last_hit    INTEGER NOT NULL,
  hits        INTEGER NOT NULL DEFAULT 0
);
CREATE INDEX IF NOT EXISTS cache_lru ON cache(last_hit);
`

// Open opens (creating) the state database.
func Open(path string) (*sql.DB, error) {
	abs, err := filepath.Abs(path)
	if err != nil {
		return nil, err
	}
	d, err := sql.Open("sqlite", "file:"+filepath.ToSlash(abs)+
		"?_pragma=journal_mode(WAL)&_pragma=busy_timeout(30000)&_pragma=synchronous(NORMAL)")
	if err != nil {
		return nil, err
	}
	// one connection: sqlite serializes writes anyway, and nobody ever
	// waits for a second one. Never hold a *sql.Rows across a call that
	// needs the database (or a lock someone holding it may want).
	d.SetMaxOpenConns(1)
	if _, err := d.Exec(schema); err != nil {
		d.Close()
		return nil, err
	}
	return d, nil
}
