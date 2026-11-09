package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"gpu-timeshare/internal/config"
)

// TestQueueCmd drives `gpu-timeshare queue` against a server whose model
// is slow enough for the queue to be seen, added to, and cleared.
func TestQueueCmd(t *testing.T) {
	e := start(t, "", `
[models.slow]
command = ["STUB", "--uds", "{socket}", "--name", "slow", "--log", "LOG", "--delay", "1s", "--start", "0s"]
concurrency = 1
`)
	run := func(client string, stdin string, args ...string) (map[string]any, error) {
		var out bytes.Buffer
		err := queueCmd(append([]string{"--server", e.url, "--token", e.tokens[client]}, args...), strings.NewReader(stdin), &out)
		var v map[string]any
		if err == nil && out.Len() > 0 {
			if jerr := json.Unmarshal(out.Bytes(), &v); jerr != nil {
				t.Fatalf("%v: not json: %s", args, out.Bytes())
			}
		}
		return v, err
	}
	pic := filepath.Join(e.dir, "a.png")
	os.WriteFile(pic, []byte("\x89PNG\r\n\x1a\nnot really"), 0o644)

	b, err := run("alice", "GIF89a from stdin", "add", "model=slow", "temperature=0", "max_tokens=8",
		"prompt=what is it?", "image="+pic, "image=-")
	if err != nil {
		t.Fatal(err)
	}
	if b["status"] != "in_progress" || b["request_counts"].(map[string]any)["total"] != 2.0 {
		t.Fatalf("add: %v", b)
	}
	// the body went in as asked: params typed, the picture as a data: URL
	reqs := e.content("alice", b["input_file_id"])
	body := reqs[1]["body"].(map[string]any)
	if body["temperature"] != 0.0 || body["max_tokens"] != 8.0 || body["model"] != "slow" {
		t.Errorf("params: %v", body)
	}
	content := body["messages"].([]any)[0].(map[string]any)["content"].([]any)
	if url := content[0].(map[string]any)["image_url"].(map[string]any)["url"].(string); !strings.HasPrefix(url, "data:image/gif;base64,") {
		t.Errorf("stdin picture: %.40s", url)
	}
	if content[1].(map[string]any)["text"] != "what is it?" {
		t.Errorf("prompt: %v", content[1])
	}
	if _, err := run("alice", "", "add", "model=slow", "image=-", "image=-"); err == nil {
		t.Error("stdin twice: no error")
	}
	if _, err := run("alice", "", "add", "image="+pic); err == nil {
		t.Error("no model: no error")
	}

	// distinct pictures: twins would share one answer and finish at once
	args := []string{"add", "model=slow", "seed=1"}
	for i := range 5 {
		p := filepath.Join(e.dir, fmt.Sprintf("b%d.png", i))
		os.WriteFile(p, []byte(fmt.Sprintf("\x89PNG\r\n\x1a\nbob %d", i)), 0o644)
		args = append(args, "image="+p)
	}
	b2, _ := run("bob", "", args...)
	q, err := run("alice", "", "query")
	if err != nil {
		t.Fatal(err)
	}
	if n := len(q["batches"].([]any)); n != 1 {
		t.Errorf("alice sees %d batches, want her own one", n)
	}
	if q["models"].([]any)[0].(map[string]any)["model"] != "slow" {
		t.Errorf("query models: %v", q["models"])
	}

	// alice's clear is alice's; root's is everyone's
	if _, err := run("alice", "", "clear"); err != nil {
		t.Fatal(err)
	}
	e.await("alice", b["id"].(string), "cancelled")
	if got := e.do("GET", "/v1/batches/"+b2["id"].(string), "bob", nil, nil).json(t)["status"]; got != "in_progress" {
		t.Errorf("bob's batch after alice's clear: %v", got)
	}
	if _, err := run("root", "", "cancel", "batch_nope"); err == nil {
		t.Error("cancel of an unknown batch: no error")
	}
	if _, err := run("root", "", "clear"); err != nil {
		t.Fatal(err)
	}
	e.await("bob", b2["id"].(string), "cancelled")
	q, _ = run("root", "", "query")
	if n := len(q["batches"].([]any)); n != 0 {
		t.Errorf("after clear: %d unfinished batches", n)
	}
	if q, _ = run("root", "", "query", "--all"); len(q["batches"].([]any)) != 2 {
		t.Errorf("--all: %v", q["batches"])
	}
}

// gpu-timeshare-admin passes --config: queue finds the server from it
func TestQueueCmdConfig(t *testing.T) {
	e := start(t, "", twoModels)
	host := strings.TrimPrefix(e.url, "http://")
	cfg := filepath.Join(e.dir, "client.toml")
	os.WriteFile(cfg, []byte(fmt.Sprintf("listen = %q\nstate_dir = %q\n[models.a]\ncommand = [\"true\", \"{port}\"]\n", host, e.dir)), 0o644)
	var out bytes.Buffer
	if err := queueCmd([]string{"query", "--token", e.tokens["root"], "--config", cfg}, nil, &out); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out.String(), `"models"`) {
		t.Errorf("query: %s", out.String())
	}
	if s, ca := localServer(&config.Config{Listen: "0.0.0.0:8100", TLS: config.TLS{Cert: "/c.crt"}}, ""); s != "https://127.0.0.1:8100" || ca != "/c.crt" {
		t.Errorf("wildcard: %s %s", s, ca)
	}
}

func TestQueueCmdBadConfig(t *testing.T) {
	err := queueCmd([]string{"query", "--token", "x", "--config", "/nonexistent.toml"}, nil, io.Discard)
	if err == nil || !strings.Contains(err.Error(), "nonexistent") {
		t.Errorf("an unreadable --config: %v", err)
	}
}
