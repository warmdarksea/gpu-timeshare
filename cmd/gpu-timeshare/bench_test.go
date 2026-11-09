package main

import (
	"bytes"
	"crypto/rand"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"io"
	"mime/multipart"
	"os"
	"strconv"
	"testing"
	"time"
)

// TestQueueThroughput times getting a batch of pictures queued: the upload,
// then the create. Not run by default: TIMESHARE_BENCH=lines[,KB per picture].
func TestQueueThroughput(t *testing.T) {
	spec := os.Getenv("TIMESHARE_BENCH")
	if spec == "" {
		t.Skip("TIMESHARE_BENCH=lines[,kb] to run")
	}
	n, kb := 200, 1500
	fmt.Sscanf(spec, "%d,%d", &n, &kb)
	e := start(t, "", `
[models.a]
command = ["STUB", "--uds", "{socket}", "--name", "a", "--log", "LOG", "--start", "0s"]
concurrency = 8
`)
	var file bytes.Buffer
	pic := make([]byte, kb*1024)
	for i := 0; i < n; i++ {
		rand.Read(pic)
		url := "data:image/jpeg;base64," + base64.StdEncoding.EncodeToString(pic)
		body, _ := json.Marshal(map[string]any{"model": "a", "temperature": 0, "max_tokens": 16,
			"messages": []map[string]any{{"role": "user", "content": []map[string]any{
				{"type": "image_url", "image_url": map[string]any{"url": url}},
				{"type": "text", "text": "describe " + strconv.Itoa(i)}}}}})
		l, _ := json.Marshal(map[string]any{"custom_id": strconv.Itoa(i), "method": "POST",
			"url": "/v1/chat/completions", "body": json.RawMessage(body)})
		file.Write(l)
		file.WriteByte('\n')
	}
	size := float64(file.Len()) / (1 << 20)

	var buf bytes.Buffer
	mw := multipart.NewWriter(&buf)
	mw.WriteField("purpose", "batch")
	fw, _ := mw.CreateFormFile("file", "in.jsonl")
	io.Copy(fw, &file)
	mw.Close()
	t0 := time.Now()
	r := e.do("POST", "/v1/files", "alice", &buf, map[string]string{"Content-Type": mw.FormDataContentType()})
	if r.status != 200 {
		t.Fatalf("upload: %d %s", r.status, r.body)
	}
	up := time.Since(t0)
	id := r.json(t)["id"].(string)
	t1 := time.Now()
	b := e.batch("alice", id, nil)
	create := time.Since(t1)
	t2 := time.Now()
	e.await("alice", b["id"].(string), "completed")
	run := time.Since(t2)
	t.Logf("BENCH %d lines, %.0f MiB: upload %v (%.0f MiB/s), create %v (%.0f MiB/s), run %v",
		n, size, up.Round(time.Millisecond), size/up.Seconds(), create.Round(time.Millisecond), size/create.Seconds(), run.Round(time.Millisecond))
}
