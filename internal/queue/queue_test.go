package queue

import (
	"path/filepath"
	"testing"
	"time"

	"gpu-timeshare/internal/db"
)

func TestKey(t *testing.T) {
	a, _ := Key("/v1/chat/completions", "m1", []byte(`{"model":"x","temperature":0,"messages":[{"role":"user","content":"hi <&>"}]}`))
	b, _ := Key("/v1/chat/completions", "m1", []byte(`{ "messages": [ {"content": "hi <&>", "role": "user"} ], "temperature": 0, "model": "x" }`))
	if a != b {
		t.Error("key order or whitespace changed the key")
	}
	for name, other := range map[string][3]string{
		"identity": {"/v1/chat/completions", "m2", `{"model":"x","temperature":0,"messages":[{"role":"user","content":"hi <&>"}]}`},
		"endpoint": {"/v1/completions", "m1", `{"model":"x","temperature":0,"messages":[{"role":"user","content":"hi <&>"}]}`},
		"number":   {"/v1/chat/completions", "m1", `{"model":"x","temperature":0.0,"messages":[{"role":"user","content":"hi <&>"}]}`},
	} {
		k, _ := Key(other[0], other[1], []byte(other[2]))
		if k == a {
			t.Errorf("a different %s, the same key", name)
		}
	}
	if _, err := Key("e", "m", []byte(`{"a":1} {"b":2}`)); err == nil {
		t.Error("two values keyed as one")
	}
}

func TestExpire(t *testing.T) {
	d, err := db.Open(filepath.Join(t.TempDir(), "t.db"))
	if err != nil {
		t.Fatal(err)
	}
	q := &Queue{DB: d}
	now := time.Now()
	add := func(key string, created, hit time.Time, size int) {
		d.Exec(`INSERT INTO cache(key, model, identity, endpoint, body, bytes, elapsed_ms, created, last_hit)
			VALUES (?, 'm', 'i', '/e', ?, ?, 1, ?, ?)`, key, make([]byte, size), size, created.Unix(), hit.Unix())
	}
	keys := func() map[string]bool {
		out := map[string]bool{}
		rows, _ := d.Query("SELECT key FROM cache")
		defer rows.Close()
		for rows.Next() {
			var k string
			rows.Scan(&k)
			out[k] = true
		}
		return out
	}
	add("old", now.Add(-48*time.Hour), now, 10)
	add("unused", now.Add(-time.Hour), now.Add(-2*time.Hour), 10)
	add("lru1", now, now.Add(-30*time.Minute), 100)
	add("lru2", now, now.Add(-10*time.Minute), 100)
	add("fresh", now, now, 100)

	if n, _ := q.Expire(Expiry{}, now); n != 0 {
		t.Errorf("no limits expired %d", n)
	}
	if n, _ := q.Expire(Expiry{MaxAge: 24 * time.Hour}, now); n != 1 || keys()["old"] {
		t.Errorf("max_age: %d gone, left %v", n, keys())
	}
	if n, _ := q.Expire(Expiry{MaxUnused: time.Hour}, now); n != 1 || keys()["unused"] {
		t.Errorf("max_unused: %d gone, left %v", n, keys())
	}
	if n, _ := q.Expire(Expiry{MaxSize: 250}, now); n != 1 || keys()["lru1"] || !keys()["lru2"] || !keys()["fresh"] {
		t.Errorf("max_size: %d gone, left %v (want the least recently used gone)", n, keys())
	}
}

func TestParseCacheControl(t *testing.T) {
	for h, want := range map[string]Policy{
		"":                          {Read: true, Write: true},
		"no-cache":                  {Write: true},
		"No-Store":                  {},
		"max-age=60":                {Read: true, Write: true, MaxAge: time.Minute},
		"max-age=0":                 {Write: true},
		"max-age=x":                 {Read: true, Write: true},
		"only-if-cached, max-age=5": {Read: true, Write: true, MaxAge: 5 * time.Second, OnlyIfCached: true},
	} {
		if got := ParseCacheControl(h); got != want {
			t.Errorf("%q: %+v, want %+v", h, got, want)
		}
	}
}
