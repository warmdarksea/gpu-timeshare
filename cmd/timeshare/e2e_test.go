package main

// End to end: the real API and scheduler, with timeshare-stub standing in
// for the model servers.

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"mime/multipart"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"

	"gpu-timeshare/internal/auth"
	"gpu-timeshare/internal/config"
	"gpu-timeshare/internal/db"
	"gpu-timeshare/internal/queue"
	"gpu-timeshare/internal/upstream"
)

var stub string

func TestMain(m *testing.M) {
	dir, err := os.MkdirTemp("", "timeshare-test")
	if err != nil {
		panic(err)
	}
	stub = filepath.Join(dir, "timeshare-stub")
	if out, err := exec.Command("go", "build", "-o", stub, "gpu-timeshare/cmd/timeshare-stub").CombinedOutput(); err != nil {
		fmt.Fprintf(os.Stderr, "building the stub: %v\n%s", err, out)
		os.Exit(1)
	}
	code := m.Run()
	os.RemoveAll(dir)
	os.Exit(code)
}

type env struct {
	t      *testing.T
	dir    string
	url    string
	log    string // the stubs' events
	tokens map[string]string
	cfg    *config.Config
	q      *queue.Queue
	logs   *bytes.Buffer
	logMu  *sync.Mutex
}

// start runs a timeshare over the given models (TOML, with STUB and LOG
// standing for the stub binary and its event log) until the test ends.
func start(t *testing.T, scheduler, models string) *env { return startTop(t, "", scheduler, models) }

func startTop(t *testing.T, top, scheduler, models string) *env {
	t.Helper()
	dir := t.TempDir()
	e := &env{t: t, dir: dir, log: filepath.Join(dir, "stub.jsonl"), tokens: map[string]string{},
		logs: &bytes.Buffer{}, logMu: &sync.Mutex{}}
	r := strings.NewReplacer("STUB", stub, "LOG", e.log, "DIR", dir)
	toml := fmt.Sprintf("state_dir = %q\n%s\n\n[scheduler]\nstop_grace = \"2s\"\n%s\n%s\n", dir, r.Replace(top),
		r.Replace(scheduler), r.Replace(models))
	path := filepath.Join(dir, "timeshare.toml")
	if err := os.WriteFile(path, []byte(toml), 0o644); err != nil {
		t.Fatal(err)
	}
	cfg, err := config.Load(path)
	if err != nil {
		t.Fatal(err)
	}
	cfg.EnsureDirs()
	d, err := db.Open(cfg.DBPath())
	if err != nil {
		t.Fatal(err)
	}
	e.cfg = cfg
	e.q = &queue.Queue{DB: d, FilesDir: cfg.FilesDir()}
	logf := func(format string, a ...any) {
		e.logMu.Lock()
		fmt.Fprintf(e.logs, format+"\n", a...)
		e.logMu.Unlock()
		t.Logf(format, a...)
	}
	h, sc := wire(cfg, d, e.q, logf)
	sc.Tick = 50 * time.Millisecond
	ts := httptest.NewServer(h)
	e.url = ts.URL
	ctx, cancel := context.WithCancel(context.Background())
	done := make(chan struct{})
	go func() { sc.Run(ctx); close(done) }()
	t.Cleanup(func() {
		cancel()
		<-done
		ts.Close()
		d.Close()
	})
	a := auth.New(d)
	for _, c := range []string{"alice", "bob"} {
		tok, err := a.Add(c, false)
		if err != nil {
			t.Fatal(err)
		}
		e.tokens[c] = tok
	}
	tok, _ := a.Add("root", true)
	e.tokens["root"] = tok
	return e
}

func (e *env) serverLog() string {
	e.logMu.Lock()
	defer e.logMu.Unlock()
	return e.logs.String()
}

type resp struct {
	status int
	header http.Header
	body   []byte
}

func (r resp) json(t *testing.T) map[string]any {
	t.Helper()
	var v map[string]any
	if err := json.Unmarshal(r.body, &v); err != nil {
		t.Fatalf("not json (%d): %s", r.status, r.body)
	}
	return v
}

func (e *env) do(method, path, client string, body io.Reader, header map[string]string) resp {
	e.t.Helper()
	req, _ := http.NewRequest(method, e.url+path, body)
	if client != "" {
		req.Header.Set("Authorization", "Bearer "+e.tokens[client])
	}
	for k, v := range header {
		req.Header.Set(k, v)
	}
	res, err := http.DefaultClient.Do(req)
	if err != nil {
		e.t.Fatal(err)
	}
	defer res.Body.Close()
	b, _ := io.ReadAll(res.Body)
	return resp{res.StatusCode, res.Header, b}
}

func chat(model, text string) string {
	b, _ := json.Marshal(map[string]any{"model": model, "temperature": 0,
		"messages": []map[string]any{{"role": "user", "content": text}}})
	return string(b)
}

func (e *env) ask(client, model, text string, header map[string]string) resp {
	e.t.Helper()
	return e.do("POST", "/v1/chat/completions", client, strings.NewReader(chat(model, text)), header)
}

type event struct {
	Event  string `json:"event"`
	Name   string `json:"name"`
	Model  string `json:"model"`
	Digest string `json:"digest"`
	PID    int    `json:"pid"`
	Child  int    `json:"child"`
	T      int64  `json:"t"`
	Inflt  int    `json:"inflight"`
}

func (e *env) events() []event {
	f, err := os.Open(e.log)
	if err != nil {
		return nil
	}
	defer f.Close()
	var out []event
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		var ev event
		json.Unmarshal(sc.Bytes(), &ev)
		out = append(out, ev)
	}
	return out
}

func (e *env) requests() []event {
	var out []event
	for _, ev := range e.events() {
		if ev.Event == "request" {
			out = append(out, ev)
		}
	}
	return out
}

func waitFor(t *testing.T, d time.Duration, what string, ok func() bool) {
	t.Helper()
	deadline := time.Now().Add(d)
	for !ok() {
		if time.Now().After(deadline) {
			t.Fatalf("timed out waiting for %s", what)
		}
		time.Sleep(50 * time.Millisecond)
	}
}

// gone: no such process, or a zombie nobody has reaped yet.
func gone(pid int) bool {
	b, err := os.ReadFile(fmt.Sprintf("/proc/%d/stat", pid))
	if err != nil {
		return true
	}
	f := strings.Fields(string(b[bytes.LastIndexByte(b, ')')+1:]))
	return len(f) > 0 && f[0] == "Z"
}

const twoModels = `
[models.a]
command = ["STUB", "--uds", "{socket}", "--name", "upstream-a", "--log", "LOG"]
cost = 0.6
concurrency = 2

[models.b]
command = ["STUB", "--port", "{port}", "--name", "upstream-b", "--log", "LOG", "--child"]
cost = 0.6
concurrency = 3
fingerprint = "weights-b"
`

func TestSingleRequests(t *testing.T) {
	e := start(t, `idle = "10m"`, twoModels)

	r := e.ask("alice", "a", "hello", nil)
	if r.status != 200 {
		t.Fatalf("%d %s", r.status, r.body)
	}
	v := r.json(t)
	if v["model"] != "a" {
		t.Errorf("model %v, want the name the client asked for", v["model"])
	}
	content := v["choices"].([]any)[0].(map[string]any)["message"].(map[string]any)["content"].(string)
	if !strings.HasPrefix(content, "upstream-a saw ") {
		t.Errorf("content %q: not from upstream-a", content)
	}
	if !bytes.Contains(r.body, []byte("<&>")) {
		t.Errorf("the reply's <&> was escaped: %s", r.body)
	}
	if r.header.Get("Cache-Status") != "gpu-timeshare; fwd=miss; stored" || r.header.Get("Age") != "" {
		t.Errorf("first answer: Cache-Status %q, Age %q", r.header.Get("Cache-Status"), r.header.Get("Age"))
	}
	if reqs := e.requests(); len(reqs) != 1 || reqs[0].Model != "upstream-a" {
		t.Fatalf("upstream saw %+v, want one request naming upstream-a", reqs)
	}

	// the same question again, from someone else: the cache
	r2 := e.ask("bob", "a", "hello", nil)
	if r2.status != 200 || r2.header.Get("Cache-Status") != "gpu-timeshare; hit" || r2.header.Get("Age") == "" {
		t.Errorf("second ask: %d Cache-Status %q Age %q", r2.status, r2.header.Get("Cache-Status"), r2.header.Get("Age"))
	}
	if !bytes.Equal(r.body, r2.body) {
		t.Errorf("a hit differs from the answer:\n%s\n%s", r.body, r2.body)
	}
	// key order doesn't make a different question
	r3 := e.do("POST", "/v1/chat/completions", "alice", strings.NewReader(
		`{"messages":[{"content":"hello","role":"user"}], "temperature":0, "model":"a"}`), nil)
	if r3.header.Get("Cache-Status") != "gpu-timeshare; hit" {
		t.Errorf("the same body, keys reordered: %q", r3.header.Get("Cache-Status"))
	}
	if n := len(e.requests()); n != 1 {
		t.Errorf("upstream saw %d requests, want 1", n)
	}
	if r := e.ask("alice", "a", "hello", map[string]string{"Cache-Control": "no-cache"}); r.header.Get("Cache-Status") != "gpu-timeshare; fwd=request; stored" {
		t.Errorf("no-cache: %q", r.header.Get("Cache-Status"))
	}
	if n := len(e.requests()); n != 2 {
		t.Errorf("after no-cache, upstream saw %d requests, want 2", n)
	}

	// b: a TCP port, and its fingerprint is the system_fingerprint
	rb := e.ask("alice", "b", "hello", nil)
	if fp := rb.json(t)["system_fingerprint"]; fp != "weights-b" {
		t.Errorf("system_fingerprint %v, want weights-b", fp)
	}

	// errors, OpenAI-shaped
	for _, c := range []struct {
		name   string
		r      resp
		status int
		code   string
	}{
		{"no token", e.do("POST", "/v1/chat/completions", "", strings.NewReader(chat("a", "x")), nil), 401, "missing_api_key"},
		{"bad token", e.do("POST", "/v1/chat/completions", "", strings.NewReader(chat("a", "x")),
			map[string]string{"Authorization": "Bearer gts_nope"}), 401, "invalid_api_key"},
		{"unknown model", e.ask("alice", "zzz", "x", nil), 404, "model_not_found"},
		{"stream", e.do("POST", "/v1/chat/completions", "alice", strings.NewReader(`{"model":"a","stream":true}`), nil), 400, ""},
		{"not json", e.do("POST", "/v1/chat/completions", "alice", strings.NewReader(`{`), nil), 400, ""},
		{"endpoint not served", e.do("POST", "/v1/embeddings2", "alice", strings.NewReader(chat("a", "x")), nil), 404, "unknown_url"},
	} {
		if c.r.status != c.status {
			t.Errorf("%s: %d, want %d: %s", c.name, c.r.status, c.status, c.r.body)
			continue
		}
		er, _ := c.r.json(t)["error"].(map[string]any)
		if er == nil || er["message"] == "" {
			t.Errorf("%s: not an OpenAI error: %s", c.name, c.r.body)
		} else if c.code != "" && er["code"] != c.code {
			t.Errorf("%s: code %v, want %s", c.name, er["code"], c.code)
		}
	}

	// a 400 from the model is its answer: passed on, not cached, not retried
	before := len(e.requests())
	for range 2 {
		if r := e.ask("alice", "a", "bad-request", nil); r.status != 400 {
			t.Errorf("bad-request: %d %s", r.status, r.body)
		}
	}
	if n := len(e.requests()) - before; n != 2 {
		t.Errorf("a 400 went upstream %d times for 2 asks, want 2 (not cached)", n)
	}
	// a 500 is retried, then fails
	before = len(e.requests())
	if r := e.ask("alice", "a", "please-fail", nil); r.status != 502 {
		t.Errorf("please-fail: %d %s", r.status, r.body)
	} else if code := r.json(t)["error"].(map[string]any)["code"]; code != "model_error" {
		t.Errorf("please-fail: code %v", code)
	}
	if n := len(e.requests()) - before; n != 3 {
		t.Errorf("a failing request went upstream %d times, want 3 (max_attempts)", n)
	}

	// /v1/models lists the config's names
	m := e.do("GET", "/v1/models", "bob", nil, nil).json(t)
	if data := m["data"].([]any); len(data) != 2 || data[0].(map[string]any)["id"] != "a" {
		t.Errorf("/v1/models: %v", m)
	}
	var n int
	e.q.DB.QueryRow("SELECT COUNT(*) FROM requests").Scan(&n)
	if n != 0 {
		t.Errorf("%d request rows left after every answer was delivered", n)
	}
}

func upload(e *env, client string, lines []string) string {
	e.t.Helper()
	var buf bytes.Buffer
	mw := multipart.NewWriter(&buf)
	mw.WriteField("purpose", "batch")
	fw, _ := mw.CreateFormFile("file", "in.jsonl")
	io.WriteString(fw, strings.Join(lines, "\n")+"\n")
	mw.Close()
	r := e.do("POST", "/v1/files", client, &buf, map[string]string{"Content-Type": mw.FormDataContentType()})
	if r.status != 200 {
		e.t.Fatalf("upload: %d %s", r.status, r.body)
	}
	return r.json(e.t)["id"].(string)
}

func line(id, model, text string) string {
	b, _ := json.Marshal(map[string]any{"custom_id": id, "method": "POST", "url": "/v1/chat/completions",
		"body": json.RawMessage(chat(model, text))})
	return string(b)
}

func (e *env) batch(client, file string, header map[string]string) map[string]any {
	e.t.Helper()
	r := e.do("POST", "/v1/batches", client, strings.NewReader(fmt.Sprintf(
		`{"input_file_id": %q, "endpoint": "/v1/chat/completions", "completion_window": "24h", "metadata": {"run": "test"}}`, file)), header)
	if r.status != 200 {
		e.t.Fatalf("create batch: %d %s", r.status, r.body)
	}
	return r.json(e.t)
}

func (e *env) await(client, id string, final string) map[string]any {
	e.t.Helper()
	var b map[string]any
	waitFor(e.t, 30*time.Second, "batch "+id+" to be "+final, func() bool {
		b = e.do("GET", "/v1/batches/"+id, client, nil, nil).json(e.t)
		return b["status"] == final
	})
	return b
}

func (e *env) content(client string, id any) []map[string]any {
	e.t.Helper()
	if id == nil {
		return nil
	}
	r := e.do("GET", "/v1/files/"+id.(string)+"/content", client, nil, nil)
	if r.status != 200 {
		e.t.Fatalf("file content: %d %s", r.status, r.body)
	}
	var out []map[string]any
	for _, l := range strings.Split(strings.TrimSpace(string(r.body)), "\n") {
		var v map[string]any
		if err := json.Unmarshal([]byte(l), &v); err != nil {
			e.t.Fatalf("output line %q: %v", l, err)
		}
		out = append(out, v)
	}
	return out
}

// The point of the thing: batches for two models from two clients, all
// queued at once, are answered one model at a time -- every request for the
// loaded model before the card switches -- not in the order they arrived.
func TestBatchTimeshares(t *testing.T) {
	e := start(t, `idle = "10m"`, twoModels)

	var aliceA, aliceB, bob []string
	for i := range 3 {
		aliceA = append(aliceA, line(fmt.Sprintf("al-a-%d", i), "a", fmt.Sprintf("picture %d", i)))
		aliceB = append(aliceB, line(fmt.Sprintf("al-b-%d", i), "b", fmt.Sprintf("picture %d", i)))
	}
	aliceB = append(aliceB, line("al-fail", "b", "please-fail"))
	for i := range 4 {
		bob = append(bob, line(fmt.Sprintf("bob-%d", i), "a", fmt.Sprintf("bob picture %d", i)))
	}
	fa, fbB, fb := upload(e, "alice", aliceA), upload(e, "alice", aliceB), upload(e, "bob", bob)

	// privacy: bob can't see or use alice's file
	if r := e.do("GET", "/v1/files/"+fa, "bob", nil, nil); r.status != 404 {
		t.Errorf("bob reading alice's file: %d", r.status)
	}
	r := e.do("POST", "/v1/batches", "bob", strings.NewReader(fmt.Sprintf(
		`{"input_file_id": %q, "endpoint": "/v1/chat/completions", "completion_window": "24h"}`, fa)), nil)
	if r.status != 400 {
		t.Errorf("bob batching alice's file: %d %s", r.status, r.body)
	}

	// b's batch first: arrival order is not answer order
	bab, baa, bb := e.batch("alice", fbB, nil), e.batch("alice", fa, nil), e.batch("bob", fb, nil)
	if baa["object"] != "batch" || baa["status"] != "in_progress" || baa["metadata"].(map[string]any)["run"] != "test" {
		t.Errorf("created: %v", baa)
	}
	if r := e.do("GET", "/v1/batches/"+baa["id"].(string), "bob", nil, nil); r.status != 404 {
		t.Errorf("bob reading alice's batch: %d", r.status)
	}
	baa = e.await("alice", baa["id"].(string), "completed")
	bab = e.await("alice", bab["id"].(string), "completed")
	bb = e.await("bob", bb["id"].(string), "completed")

	if c := bab["request_counts"].(map[string]any); c["total"] != 4.0 || c["completed"] != 3.0 || c["failed"] != 1.0 {
		t.Errorf("alice's b counts: %v", c)
	}
	out := e.content("alice", baa["output_file_id"])
	if len(out) != 3 {
		t.Fatalf("alice's a output: %d lines", len(out))
	}
	for i, l := range out {
		if l["custom_id"] != fmt.Sprintf("al-a-%d", i) {
			t.Errorf("output line %d is %v: not in input order", i, l["custom_id"])
		}
		res := l["response"].(map[string]any)
		body := res["body"].(map[string]any)
		if res["status_code"] != 200.0 || body["model"] != "a" {
			t.Errorf("output line %d: %v", i, l)
		}
	}
	errs := e.content("alice", bab["error_file_id"])
	if len(errs) != 1 || errs[0]["custom_id"] != "al-fail" || errs[0]["error"].(map[string]any)["code"] != "model_error" {
		t.Errorf("alice's b errors: %v", errs)
	}
	if n := len(e.content("bob", bb["output_file_id"])); n != 4 {
		t.Errorf("bob's output: %d lines", n)
	}
	if r := e.do("GET", "/v1/files/"+baa["output_file_id"].(string)+"/content", "bob", nil, nil); r.status != 404 {
		t.Errorf("bob reading alice's results: %d", r.status)
	}
	if r := e.do("GET", "/v1/files/"+baa["output_file_id"].(string), "root", nil, nil); r.status != 200 {
		t.Errorf("admin reading alice's results: %d", r.status)
	}

	// one switch: every a (alice's and bob's), then every b
	var names []string
	for _, ev := range e.requests() {
		if len(names) == 0 || names[len(names)-1] != ev.Name {
			names = append(names, ev.Name)
		}
	}
	if len(names) != 2 {
		t.Errorf("upstream order switched models %d times: %v", len(names)-1, names)
	}
	// and they were never up together (0.6 + 0.6 > 1)
	var starts []string
	for _, ev := range e.events() {
		if ev.Event == "start" {
			starts = append(starts, ev.Name)
		}
	}
	if len(starts) != 2 {
		t.Errorf("servers started: %v, want each once", starts)
	}
	for _, ev := range e.requests() {
		if ev.Name == "upstream-a" && ev.Inflt > 2 || ev.Name == "upstream-b" && ev.Inflt > 3 {
			t.Errorf("%s had %d in flight, over its concurrency", ev.Name, ev.Inflt)
		}
	}

	// list, newest first
	l := e.do("GET", "/v1/batches?limit=10", "root", nil, nil).json(t)
	if data := l["data"].([]any); len(data) != 3 || l["has_more"] != false {
		t.Errorf("admin's list: %v", l)
	}
	if data := e.do("GET", "/v1/batches", "bob", nil, nil).json(t)["data"].([]any); len(data) != 1 {
		t.Errorf("bob's list has %d batches, want his 1", len(data))
	}

	// the same files again: all from the cache, nothing upstream
	before := len(e.requests())
	again := e.await("alice", e.batch("alice", fa, nil)["id"].(string), "completed")
	e.await("alice", e.batch("alice", fbB, nil)["id"].(string), "completed")
	if n := len(e.requests()) - before; n != 3 { // the 3 attempts of please-fail; failures aren't cached
		t.Errorf("repeated batches went upstream %d times, want 3", n)
	}
	if got := e.content("alice", again["output_file_id"]); len(got) != 3 {
		t.Errorf("repeated batch: %d answers", len(got))
	} else if g, w := got[1]["response"].(map[string]any)["body"], out[1]["response"].(map[string]any)["body"]; fmt.Sprint(g) != fmt.Sprint(w) {
		t.Errorf("a cached answer differs:\n%v\n%v", g, w)
	}
	// and with no-cache, everything goes upstream again
	before = len(e.requests())
	e.await("bob", e.batch("bob", fb, map[string]string{"Cache-Control": "no-cache"})["id"].(string), "completed")
	if n := len(e.requests()) - before; n != 4 {
		t.Errorf("a no-cache batch went upstream %d times, want 4", n)
	}

	var n int
	e.q.DB.QueryRow("SELECT COUNT(*) FROM requests").Scan(&n)
	if n != 0 {
		t.Errorf("%d request rows left after every batch finished", n)
	}
	// an input file whose batches ended can be deleted
	if r := e.do("DELETE", "/v1/files/"+fa, "alice", nil, nil); r.status != 200 {
		t.Errorf("deleting a finished batch's input: %d %s", r.status, r.body)
	}
}

func TestBatchValidation(t *testing.T) {
	e := start(t, `idle = "10m"`, twoModels)
	f := upload(e, "alice", []string{line("x", "a", "1"), line("x", "a", "2"), `{"custom_id": "y", "method": "GET", "url": "/v1/chat/completions", "body": {}}`, `nope`,
		line("z", "b", "a second model"), line("w", "nope", "an unknown one")})
	b := e.batch("alice", f, nil)
	if b["status"] != "failed" {
		t.Fatalf("a bad file made a %v batch", b["status"])
	}
	var codes []string
	for _, x := range b["errors"].(map[string]any)["data"].([]any) {
		codes = append(codes, x.(map[string]any)["code"].(string))
	}
	if strings.Join(codes, ",") != "duplicate_custom_id,invalid_request,invalid_json_line,mismatched_model,mismatched_model" {
		t.Errorf("errors: %v", codes)
	}
	for _, c := range []struct{ body, param string }{
		{`{"endpoint": "/v1/chat/completions", "completion_window": "24h"}`, "input_file_id"},
		{fmt.Sprintf(`{"input_file_id": %q, "endpoint": "/v1/nope", "completion_window": "24h"}`, f), "endpoint"},
		{fmt.Sprintf(`{"input_file_id": %q, "endpoint": "/v1/chat/completions", "completion_window": "9999h"}`, f), "completion_window"},
	} {
		r := e.do("POST", "/v1/batches", "alice", strings.NewReader(c.body), nil)
		if r.status != 400 || r.json(t)["error"].(map[string]any)["param"] != c.param {
			t.Errorf("%s: %d %s", c.body, r.status, r.body)
		}
	}
}

func TestIdleUnloadKillsTheGroup(t *testing.T) {
	e := start(t, `idle = "1s"`, twoModels)
	if r := e.ask("alice", "b", "hi", nil); r.status != 200 {
		t.Fatalf("%d %s", r.status, r.body)
	}
	var pid, child int
	for _, ev := range e.events() {
		if ev.Event == "child" {
			pid, child = ev.PID, ev.Child
		}
	}
	if pid == 0 || child == 0 {
		t.Fatal("the stub logged no child")
	}
	waitFor(t, 10*time.Second, "b to be stopped for idleness", func() bool { return gone(pid) && gone(child) })
	if !strings.Contains(e.serverLog(), "b: idle for") {
		t.Errorf("no idle line in the log:\n%s", e.serverLog())
	}
	st := e.do("GET", "/v1/timeshare/status", "alice", nil, nil).json(t)
	for _, m := range st["models"].([]any) {
		if m.(map[string]any)["state"] != "down" {
			t.Errorf("after idling: %v", m)
		}
	}
	// and it comes back when asked
	if r := e.ask("alice", "b", "again", nil); r.status != 200 {
		t.Fatalf("after idling: %d %s", r.status, r.body)
	}
}

func TestExpireAndCancel(t *testing.T) {
	e := start(t, `idle = "10m"`, `
[models.slow]
command = ["STUB", "--uds", "{socket}", "--name", "slow", "--log", "LOG", "--delay", "400ms", "--start", "0s"]
concurrency = 1
`)
	var lines []string
	for i := range 20 {
		lines = append(lines, line(fmt.Sprintf("s-%d", i), "slow", fmt.Sprint(i)))
	}
	f := upload(e, "alice", lines)
	r := e.do("POST", "/v1/batches", "alice", strings.NewReader(fmt.Sprintf(
		`{"input_file_id": %q, "endpoint": "/v1/chat/completions", "completion_window": "1500ms"}`, f)), nil)
	if r.status != 200 {
		t.Fatalf("%d %s", r.status, r.body)
	}
	b := e.await("alice", r.json(t)["id"].(string), "expired")
	c := b["request_counts"].(map[string]any)
	done, failed := c["completed"].(float64), c["failed"].(float64)
	if done < 1 || done > 8 || done+failed != 20 {
		t.Errorf("expired batch counts: %v", c)
	}
	if b["expired_at"] == nil {
		t.Error("no expired_at")
	}
	for _, l := range e.content("alice", b["error_file_id"]) {
		if l["error"].(map[string]any)["code"] != "batch_expired" {
			t.Errorf("an expired line: %v", l)
		}
	}

	b2 := e.batch("bob", upload(e, "bob", lines), map[string]string{"Cache-Control": "no-cache"})
	time.Sleep(700 * time.Millisecond)
	r = e.do("POST", "/v1/batches/"+b2["id"].(string)+"/cancel", "bob", nil, nil)
	if st := r.json(t)["status"]; st != "cancelling" && st != "cancelled" {
		t.Errorf("cancel: %v", st)
	}
	b2 = e.await("bob", b2["id"].(string), "cancelled")
	if c := b2["request_counts"].(map[string]any); c["completed"].(float64) < 1 || c["failed"].(float64) < 10 {
		t.Errorf("cancelled counts: %v", c)
	}
}

// A server that dies at work is restarted once; the second death marks it
// broken, and what is queued for it fails instead of waiting for ever.
func TestCrashingModel(t *testing.T) {
	e := start(t, `idle = "10m"
max_attempts = 5`, `
[models.flaky]
command = ["STUB", "--port", "{port}", "--name", "flaky", "--log", "LOG", "--exit-after", "1", "--start", "0s", "--delay", "100ms"]
concurrency = 1
`)
	var lines []string
	for i := range 6 {
		lines = append(lines, line(fmt.Sprintf("f-%d", i), "flaky", fmt.Sprint(i)))
	}
	b := e.await("alice", e.batch("alice", upload(e, "alice", lines), nil)["id"].(string), "completed")
	c := b["request_counts"].(map[string]any)
	if c["completed"].(float64) < 1 || c["failed"].(float64) < 1 || c["completed"].(float64)+c["failed"].(float64) != 6 {
		t.Errorf("counts: %v", c)
	}
	codes := map[string]bool{}
	for _, l := range e.content("alice", b["error_file_id"]) {
		codes[l["error"].(map[string]any)["code"].(string)] = true
	}
	if !codes["model_unavailable"] {
		t.Errorf("error codes %v, want model_unavailable", codes)
	}
	if !strings.Contains(e.serverLog(), "flaky: refusing its requests") {
		t.Errorf("no broken line:\n%s", e.serverLog())
	}
	st := e.do("GET", "/v1/timeshare/status", "alice", nil, nil).json(t)
	if m := st["models"].([]any)[0].(map[string]any); m["unavailable"] == nil {
		t.Errorf("status doesn't say flaky is unavailable: %v", m)
	}
}

// Unit mode, with a fake systemctl that runs the stub in the background
// the way systemd would run the unit.
func TestUnit(t *testing.T) {
	e := startTop(t, `systemctl = ["DIR/systemctl"]`, `idle = "1s"`, `
[models.u]
unit = "timeshare-model-u.service"
url = "unix:DIR/u.sock"
`)
	script := fmt.Sprintf(`#!/bin/sh
echo "$*" >> %[1]s/calls
cmd=$1; shift
case $cmd in
  reset-failed) exit 0 ;;
  start)
    [ "$1" = --no-block ] && shift
    rm -f %[1]s/u.sock
    %[2]s --uds %[1]s/u.sock --name unit-model --log %[3]s --start 200ms >/dev/null 2>&1 &
    echo $! > %[1]s/$1.pid ;;
  stop)
    for u in "$@"; do
      if [ -f %[1]s/$u.pid ]; then kill $(cat %[1]s/$u.pid) 2>/dev/null; rm -f %[1]s/$u.pid; fi
    done ;;
  show)
    for u; do :; done
    if [ -f %[1]s/$u.pid ] && kill -0 $(cat %[1]s/$u.pid) 2>/dev/null; then echo active; else echo inactive; fi ;;
esac
`, e.dir, stub, e.log)
	if err := os.WriteFile(filepath.Join(e.dir, "systemctl"), []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	r := e.ask("alice", "u", "hello", nil)
	if r.status != 200 || r.json(t)["model"] != "u" {
		t.Fatalf("%d %s", r.status, r.body)
	}
	if reqs := e.requests(); len(reqs) != 1 || reqs[0].Model != "unit-model" {
		t.Errorf("upstream saw %+v", reqs)
	}
	pid := e.requests()[0].PID
	waitFor(t, 10*time.Second, "the unit to be stopped for idleness", func() bool { return gone(pid) })
	b, _ := os.ReadFile(filepath.Join(e.dir, "calls"))
	var verbs []string
	for _, l := range strings.Split(strings.TrimSpace(string(b)), "\n") {
		if f := strings.Fields(l); f[0] != "show" {
			verbs = append(verbs, strings.Join(f, " "))
		}
	}
	want := "reset-failed timeshare-model-u.service,start --no-block timeshare-model-u.service,stop timeshare-model-u.service"
	if strings.Join(verbs, ",") != want {
		t.Errorf("systemctl calls:\n%s\nwant\n%s", strings.Join(verbs, "\n"), strings.ReplaceAll(want, ",", "\n"))
	}
	// at start-up, every unit-run model is stopped (one left by a crash)
	os.Remove(filepath.Join(e.dir, "calls"))
	if err := upstream.StopUnits(e.cfg); err != nil {
		t.Fatal(err)
	}
	if b, _ := os.ReadFile(filepath.Join(e.dir, "calls")); strings.TrimSpace(string(b)) != "stop timeshare-model-u.service" {
		t.Errorf("StopUnits ran %q", b)
	}
}

// Cache-Control on a request decides what the cache may do for it.
func TestCacheControl(t *testing.T) {
	e := start(t, `idle = "10m"`, twoModels)
	h := func(v string) map[string]string { return map[string]string{"Cache-Control": v} }

	// only-if-cached on a question never asked: 504, and no model starts
	r := e.ask("alice", "a", "q1", h("only-if-cached"))
	if r.status != 504 || r.json(t)["error"].(map[string]any)["code"] != "not_cached" {
		t.Errorf("only-if-cached miss: %d %s", r.status, r.body)
	}
	time.Sleep(300 * time.Millisecond)
	if len(e.events()) != 0 {
		t.Errorf("only-if-cached started a model: %v", e.events())
	}

	// no-store: asked, not kept
	if r := e.ask("alice", "a", "q1", h("no-store")); r.header.Get("Cache-Status") != "gpu-timeshare; fwd=request" {
		t.Errorf("no-store: %q", r.header.Get("Cache-Status"))
	}
	if r := e.ask("alice", "a", "q1", h("only-if-cached")); r.status != 504 {
		t.Errorf("after no-store, only-if-cached found something: %d", r.status)
	}
	e.ask("alice", "a", "q1", nil)
	if r := e.ask("alice", "a", "q1", h("only-if-cached")); r.status != 200 || r.header.Get("Cache-Status") != "gpu-timeshare; hit" {
		t.Errorf("only-if-cached hit: %d %q", r.status, r.header.Get("Cache-Status"))
	}

	// max-age: an answer older than asked for is not served
	time.Sleep(2100 * time.Millisecond)
	before := len(e.requests())
	if r := e.ask("alice", "a", "q1", h("max-age=60")); r.header.Get("Cache-Status") != "gpu-timeshare; hit" {
		t.Errorf("max-age=60: %q", r.header.Get("Cache-Status"))
	} else if age := r.header.Get("Age"); age != "2" && age != "3" {
		t.Errorf("Age %q, want ~2", age)
	}
	if r := e.ask("alice", "a", "q1", h("max-age=1")); r.header.Get("Cache-Status") != "gpu-timeshare; fwd=miss; stored" {
		t.Errorf("max-age=1: %q", r.header.Get("Cache-Status"))
	}
	if r := e.ask("alice", "a", "q1", h("max-age=0")); r.header.Get("Cache-Status") != "gpu-timeshare; fwd=request; stored" {
		t.Errorf("max-age=0: %q", r.header.Get("Cache-Status"))
	}
	if n := len(e.requests()) - before; n != 2 {
		t.Errorf("max-age asks went upstream %d times, want 2", n)
	}

	// the same question twice at once: asked once, the twin gets that answer
	before = len(e.requests())
	var wg sync.WaitGroup
	statuses := make([]string, 2)
	for i := range 2 {
		wg.Add(1)
		go func() {
			defer wg.Done()
			statuses[i] = e.ask([]string{"alice", "bob"}[i], "b", "twins", nil).header.Get("Cache-Status")
		}()
	}
	wg.Wait()
	if n := len(e.requests()) - before; n != 1 {
		t.Errorf("two identical requests in flight went upstream %d times", n)
	}
	got := strings.Join(statuses, " | ")
	if !strings.Contains(got, "fwd=miss; stored") || !(strings.Contains(got, "collapsed") || strings.Contains(got, "; hit")) {
		t.Errorf("twins' Cache-Status: %s", got)
	}

	// a batch: only-if-cached answers what's cached and fails the rest at once
	f := upload(e, "alice", []string{line("x", "a", "q1"), line("y", "a", "never asked")})
	b := e.await("alice", e.batch("alice", f, h("only-if-cached"))["id"].(string), "completed")
	out, errs := e.content("alice", b["output_file_id"]), e.content("alice", b["error_file_id"])
	if len(out) != 1 || out[0]["response"].(map[string]any)["cache_status"] != "gpu-timeshare; hit" {
		t.Errorf("only-if-cached batch output: %v", out)
	}
	if len(errs) != 1 || errs[0]["error"].(map[string]any)["code"] != "not_cached" {
		t.Errorf("only-if-cached batch errors: %v", errs)
	}
}

// One model per batch, as OpenAI has it; a model this server doesn't have
// fails the batch at validation, as OpenAI's would.
func TestBatchOneModel(t *testing.T) {
	e := start(t, `idle = "10m"`, twoModels)
	b := e.batch("alice", upload(e, "alice", []string{line("x", "nope", "1"), line("y", "nope", "2")}), nil)
	if b["status"] != "failed" {
		t.Fatalf("an unknown model's batch is %v", b["status"])
	}
	if code := b["errors"].(map[string]any)["data"].([]any)[0].(map[string]any)["code"]; code != "model_not_found" {
		t.Errorf("code %v", code)
	}
	b = e.batch("alice", upload(e, "alice", []string{line("x", "a", "1"), line("y", "b", "2")}), nil)
	if b["status"] != "failed" {
		t.Fatalf("a mixed batch is %v", b["status"])
	}
	er := b["errors"].(map[string]any)["data"].([]any)[0].(map[string]any)
	if er["code"] != "mismatched_model" || er["line"] != 2.0 {
		t.Errorf("mixed batch error: %v", er)
	}
	if n := len(e.requests()); n != 0 {
		t.Errorf("a failed batch asked upstream %d times", n)
	}
}
