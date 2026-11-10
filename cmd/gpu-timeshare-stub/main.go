// gpu-timeshare-stub is a fake OpenAI server for tests: a model server that
// starts slowly, answers chat completions with a digest of what it was
// asked, and logs every request, so a test can assert what the scheduler
// sent where and when.
//
//	gpu-timeshare-stub (--port N | --uds PATH) [--name NAME] [--start 0.5s] [--delay 50ms] [--log FILE]
//
// A request whose body contains "please-fail" gets a 500, "bad-request" a
// 400. With --exit-after N it exits after N answers (a crash at work).
// With --child it forks a sleeping child into its process group, which a
// clean stop must take down too (its pid goes in --log).
package main

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
	"os/exec"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

func main() {
	port := flag.Int("port", 0, "TCP port on 127.0.0.1")
	uds := flag.String("uds", "", "unix socket path")
	name := flag.String("name", "stub", "the model name it serves")
	start := flag.Duration("start", 300*time.Millisecond, "how long it takes to load")
	delay := flag.Duration("delay", 20*time.Millisecond, "per request")
	logPath := flag.String("log", "", "append one JSON line per event")
	exitAfter := flag.Int("exit-after", 0, "exit after this many answers")
	child := flag.Bool("child", false, "fork a sleeping child")
	probeRead := flag.String("probe-read", "", "try to read these files (comma-separated) and say how it went, on stderr")
	probeDial := flag.String("probe-dial", "", "try to connect to these host:ports and say how it went, on stderr")
	flag.Parse()

	var mu sync.Mutex
	logf := func(v map[string]any) {
		if *logPath == "" {
			return
		}
		mu.Lock()
		defer mu.Unlock()
		v["t"] = time.Now().UnixNano()
		v["name"] = *name
		v["pid"] = os.Getpid()
		b, _ := json.Marshal(v)
		f, err := os.OpenFile(*logPath, os.O_WRONLY|os.O_CREATE|os.O_APPEND, 0o644)
		if err != nil {
			return
		}
		f.Write(append(b, '\n'))
		f.Close()
	}
	if *child {
		c := exec.Command("sleep", "3600")
		if err := c.Start(); err == nil {
			logf(map[string]any{"event": "child", "child": c.Process.Pid})
		}
	}
	logf(map[string]any{"event": "start", "gpu": os.Getenv("CUDA_VISIBLE_DEVICES")})
	probe(*probeRead, *probeDial)
	time.Sleep(*start)

	var answered, inflight, peak atomic.Int64
	mux := http.NewServeMux()
	mux.HandleFunc("GET /v1/models", func(w http.ResponseWriter, r *http.Request) {
		fmt.Fprintf(w, `{"object":"list","data":[{"id":%q,"object":"model","owned_by":"stub"}]}`, *name)
	})
	mux.HandleFunc("GET /health", func(w http.ResponseWriter, r *http.Request) {})
	answer := func(w http.ResponseWriter, r *http.Request) {
		body, _ := io.ReadAll(r.Body)
		n := inflight.Add(1)
		defer inflight.Add(-1)
		for {
			p := peak.Load()
			if n <= p || peak.CompareAndSwap(p, n) {
				break
			}
		}
		var req struct {
			Model string `json:"model"`
		}
		json.Unmarshal(body, &req)
		h := sha256.Sum256(body)
		digest := hex.EncodeToString(h[:8])
		logf(map[string]any{"event": "request", "path": r.URL.Path, "model": req.Model, "digest": digest,
			"inflight": n, "bytes": len(body)})
		time.Sleep(*delay)
		switch {
		case strings.Contains(string(body), "please-fail"):
			http.Error(w, `{"error":{"message":"asked to fail"}}`, 500)
			return
		case strings.Contains(string(body), "bad-request"):
			http.Error(w, `{"error":{"message":"asked for a 400"}}`, 400)
			return
		}
		w.Header().Set("content-type", "application/json")
		fmt.Fprintf(w, `{"id":"chatcmpl-%s","object":"chat.completion","created":%d,"model":%q,"system_fingerprint":null,`+
			`"choices":[{"index":0,"message":{"role":"assistant","content":%q},"finish_reason":"stop"}],`+
			`"usage":{"prompt_tokens":%d,"completion_tokens":3,"total_tokens":%d}}`,
			digest, time.Now().Unix(), req.Model, *name+" saw "+digest+" <&>", len(body), len(body)+3)
		if *exitAfter > 0 && answered.Add(1) >= int64(*exitAfter) {
			go func() { time.Sleep(10 * time.Millisecond); logf(map[string]any{"event": "crash"}); os.Exit(3) }()
		}
	}
	mux.HandleFunc("POST /v1/chat/completions", answer)
	mux.HandleFunc("POST /v1/completions", answer)

	var ln net.Listener
	var err error
	if *uds != "" {
		ln, err = net.Listen("unix", *uds)
	} else {
		ln, err = net.Listen("tcp", fmt.Sprintf("127.0.0.1:%d", *port))
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	logf(map[string]any{"event": "ready"})
	http.Serve(ln, mux)
}

// probe tries what a sandbox should forbid and reports each attempt as
// "probe read PATH: ok|ERROR" / "probe dial ADDR: ok|ERROR" on stderr.
func probe(reads, dials string) {
	for _, p := range strings.Split(reads, ",") {
		if p == "" {
			continue
		}
		_, err := os.ReadFile(p)
		fmt.Fprintf(os.Stderr, "probe read %s: %s\n", p, result(err))
	}
	for _, a := range strings.Split(dials, ",") {
		if a == "" {
			continue
		}
		c, err := net.DialTimeout("tcp", a, 3*time.Second)
		if err == nil {
			c.Close()
		}
		fmt.Fprintf(os.Stderr, "probe dial %s: %s\n", a, result(err))
	}
}

func result(err error) string {
	if err == nil {
		return "ok"
	}
	return "ERROR " + err.Error()
}
