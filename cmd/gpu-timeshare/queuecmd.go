package main

// gpu-timeshare queue: the queue from the command line, as a client of a
// running server (the API, not the database: the server owns its queue).
//
//	queue query [--all]          json: each model's state and queue, and the batches
//	queue cancel BATCH...        cancel those batches
//	queue clear                  cancel every unfinished batch this token sees
//	queue add model=M image=FILE|- [prompt=TEXT] [KEY=VALUE...]
//
// add queues one chat request per image= as one batch and prints the
// batch. Other KEY=VALUEs go into each request's body: a VALUE that parses
// as JSON is that JSON (temperature=0, max_tokens=64, stop=["\n"]), anything
// else a string.

import (
	"bytes"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"mime/multipart"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"time"

	"gpu-timeshare/internal/config"
	"gpu-timeshare/internal/tlsutil"
)

const queueUsage = `usage: gpu-timeshare queue query [--all] | cancel BATCH... | clear
                         | add model=M image=FILE|- [image=...] [prompt=TEXT] [KEY=VALUE...]
  --server URL   ($TIMESHARE_SERVER; default: the --config server on this machine, else http://127.0.0.1:8100)
  --config FILE  ($TIMESHARE_CONFIG, ./timeshare.toml) gpu-timeshare-admin passes it: its listen and cert
  --token T      ($TIMESHARE_TOKEN; an admin token sees and clears every client's batches)
  --cacert FILE  ($TIMESHARE_CACERT) the server's certificate, for a self-signed one`

type client struct {
	server, token string
	http          *http.Client
}

// call does one API call and decodes its JSON answer into out (if not nil).
func (c *client) call(method, path, ctype string, body io.Reader, out any) error {
	req, err := http.NewRequest(method, c.server+path, body)
	if err != nil {
		return err
	}
	req.Header.Set("Authorization", "Bearer "+c.token)
	if ctype != "" {
		req.Header.Set("Content-Type", ctype)
	}
	res, err := c.http.Do(req)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	b, err := io.ReadAll(res.Body)
	if err != nil {
		return err
	}
	if res.StatusCode != 200 {
		var e struct {
			Error struct{ Message string } `json:"error"`
		}
		if json.Unmarshal(b, &e) == nil && e.Error.Message != "" {
			return fmt.Errorf("%s %s: %d: %s", method, path, res.StatusCode, e.Error.Message)
		}
		return fmt.Errorf("%s %s: %d: %s", method, path, res.StatusCode, strings.TrimSpace(string(b)))
	}
	if out != nil {
		return json.Unmarshal(b, out)
	}
	return nil
}

// batches lists every batch the token sees, newest first.
func (c *client) batches() ([]map[string]any, error) {
	var all []map[string]any
	after := ""
	for {
		var page struct {
			Data    []map[string]any `json:"data"`
			HasMore bool             `json:"has_more"`
			LastID  string           `json:"last_id"`
		}
		path := "/v1/batches?limit=100"
		if after != "" {
			path += "&after=" + after
		}
		if err := c.call("GET", path, "", nil, &page); err != nil {
			return nil, err
		}
		all = append(all, page.Data...)
		if !page.HasMore || page.LastID == "" {
			return all, nil
		}
		after = page.LastID
	}
}

// unfinished: a batch that still has (or may have) work queued.
func unfinished(b map[string]any) bool {
	switch b["status"] {
	case "validating", "in_progress", "finalizing", "cancelling", "expiring":
		return true
	}
	return false
}

func queueCmd(args []string, stdin io.Reader, stdout io.Writer) error {
	fs := flag.NewFlagSet("queue", flag.ExitOnError)
	fs.Usage = func() { fmt.Fprintln(os.Stderr, queueUsage) }
	env := func(k, def string) string {
		if v := os.Getenv(k); v != "" {
			return v
		}
		return def
	}
	server := fs.String("server", os.Getenv("TIMESHARE_SERVER"), "")
	token := fs.String("token", env("TIMESHARE_TOKEN", ""), "")
	cacert := fs.String("cacert", os.Getenv("TIMESHARE_CACERT"), "")
	cfgPath := configFlag(fs)
	all := fs.Bool("all", false, "query: finished batches too")
	pos := parse(fs, args)
	if len(pos) == 0 {
		return errors.New(queueUsage)
	}
	// on the server's own machine (gpu-timeshare-admin passes --config):
	// its listen address and certificate, unless given
	if *server == "" {
		*server = "http://127.0.0.1:8100"
		explicit := os.Getenv("TIMESHARE_CONFIG") != ""
		fs.Visit(func(f *flag.Flag) { explicit = explicit || f.Name == "config" })
		cfg, err := config.Load(*cfgPath)
		switch {
		case err == nil:
			*server, *cacert = localServer(cfg, *cacert)
		case explicit:
			return err
		}
	}
	if *token == "" {
		return errors.New("no token: --token or $TIMESHARE_TOKEN")
	}
	if tlsutil.CleartextRemote(*server) {
		fmt.Fprintf(os.Stderr, "gpu-timeshare: warning: %s is not https: the token crosses the network in the clear\n", *server)
	}
	tr := http.DefaultTransport.(*http.Transport).Clone()
	if *cacert != "" {
		cfg, err := tlsutil.ClientTLS(*cacert)
		if err != nil {
			return err
		}
		tr.TLSClientConfig = cfg
	}
	c := &client{server: strings.TrimRight(*server, "/"), token: *token, http: &http.Client{Transport: tr}}
	out := json.NewEncoder(stdout)
	out.SetIndent("", "  ")

	switch cmd, rest := pos[0], pos[1:]; {
	case cmd == "query" && len(rest) == 0:
		var st struct {
			Models []map[string]any `json:"models"`
		}
		if err := c.call("GET", "/v1/timeshare/status", "", nil, &st); err != nil {
			return err
		}
		bs, err := c.batches()
		if err != nil {
			return err
		}
		keep := []map[string]any{}
		for _, b := range bs {
			if *all || unfinished(b) {
				keep = append(keep, b)
			}
		}
		return out.Encode(map[string]any{"models": st.Models, "batches": keep})

	case cmd == "cancel" && len(rest) > 0:
		var failed error
		for _, id := range rest {
			var b map[string]any
			if err := c.call("POST", "/v1/batches/"+id+"/cancel", "", nil, &b); err != nil {
				fmt.Fprintf(os.Stderr, "gpu-timeshare: %v\n", err)
				failed = errors.New("some batches were not cancelled")
				continue
			}
			out.Encode(map[string]any{"id": b["id"], "status": b["status"]})
		}
		return failed

	case cmd == "clear" && len(rest) == 0:
		bs, err := c.batches()
		if err != nil {
			return err
		}
		n := 0
		for _, b := range bs {
			if b["status"] != "validating" && b["status"] != "in_progress" {
				continue // already ending: cancelling would change nothing
			}
			id, _ := b["id"].(string)
			if err := c.call("POST", "/v1/batches/"+id+"/cancel", "", nil, nil); err != nil {
				return err
			}
			n++
		}
		fmt.Fprintf(os.Stderr, "gpu-timeshare: %d batch(es) cancelled; what is on the card finishes\n", n)
		return nil

	case cmd == "add" && len(rest) > 0:
		return c.add(rest, stdin, out)
	}
	return errors.New(queueUsage)
}

// add builds the batch file in memory (one line per image) and queues it.
func (c *client) add(kvs []string, stdin io.Reader, out *json.Encoder) error {
	var images []string
	prompt := ""
	params := map[string]json.RawMessage{}
	for _, kv := range kvs {
		k, v, ok := strings.Cut(kv, "=")
		if !ok || k == "" {
			return fmt.Errorf("%q: want KEY=VALUE", kv)
		}
		switch k {
		case "image":
			images = append(images, v)
		case "prompt":
			prompt = v
		default:
			if json.Valid([]byte(v)) {
				params[k] = json.RawMessage(v)
			} else {
				params[k], _ = json.Marshal(v)
			}
		}
	}
	if _, ok := params["model"]; !ok {
		return errors.New("add: model= is required")
	}
	if len(images) == 0 {
		return errors.New("add: image=FILE (or image=- for stdin) is required")
	}
	dashes := 0
	for _, im := range images {
		if im == "-" {
			dashes++
		}
	}
	if dashes > 1 {
		return errors.New("add: stdin can be read once (image=- at most once)")
	}

	var file bytes.Buffer
	for i, im := range images {
		var pic []byte
		var err error
		name := im
		if im == "-" {
			pic, err = io.ReadAll(stdin)
			name = "stdin"
		} else {
			pic, err = os.ReadFile(im)
			name = filepath.Base(im)
		}
		if err != nil {
			return err
		}
		if len(pic) == 0 {
			return fmt.Errorf("%s: empty", name)
		}
		sum := sha256.Sum256(pic)
		content := []map[string]any{{"type": "image_url", "image_url": map[string]any{
			"url": "data:" + http.DetectContentType(pic) + ";base64," + base64.StdEncoding.EncodeToString(pic)}}}
		if prompt != "" {
			content = append(content, map[string]any{"type": "text", "text": prompt})
		}
		body := map[string]any{"messages": []map[string]any{{"role": "user", "content": content}}}
		for k, v := range params {
			body[k] = v
		}
		bb, err := json.Marshal(body)
		if err != nil {
			return err
		}
		// custom_id: which argument, and which picture
		line, _ := json.Marshal(map[string]any{"custom_id": fmt.Sprintf("%d:%s:%s", i, name, hex.EncodeToString(sum[:8])),
			"method": "POST", "url": "/v1/chat/completions", "body": json.RawMessage(bb)})
		file.Write(line)
		file.WriteByte('\n')
	}

	var form bytes.Buffer
	mw := multipart.NewWriter(&form)
	mw.WriteField("purpose", "batch")
	fw, _ := mw.CreateFormFile("file", fmt.Sprintf("queue-add-%d.jsonl", time.Now().Unix()))
	fw.Write(file.Bytes())
	mw.Close()
	var f struct {
		ID string `json:"id"`
	}
	if err := c.call("POST", "/v1/files", mw.FormDataContentType(), &form, &f); err != nil {
		return err
	}
	create, _ := json.Marshal(map[string]any{"input_file_id": f.ID, "endpoint": "/v1/chat/completions",
		"completion_window": "24h", "metadata": map[string]string{"by": "gpu-timeshare queue add"}})
	var b map[string]any
	if err := c.call("POST", "/v1/batches", "application/json", bytes.NewReader(create), &b); err != nil {
		return err
	}
	return out.Encode(b)
}

// localServer is the URL of the server a config describes, from its own
// machine: a wildcard listen address is reached on loopback (which the
// module's self-signed certificate covers), and its certificate is trusted
// unless cacert says otherwise.
func localServer(cfg *config.Config, cacert string) (string, string) {
	host, port, err := net.SplitHostPort(cfg.Listen)
	if err != nil {
		return "http://127.0.0.1:8100", cacert
	}
	switch host {
	case "", "0.0.0.0":
		host = "127.0.0.1"
	case "::":
		host = "::1"
	}
	scheme := "http"
	if cfg.TLS.Cert != "" {
		scheme = "https"
		if cacert == "" {
			cacert = cfg.TLS.Cert
		}
	}
	return scheme + "://" + net.JoinHostPort(host, port), cacert
}
