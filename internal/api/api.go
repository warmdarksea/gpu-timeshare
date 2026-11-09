// Package api is gpu-timeshare's HTTP face: the OpenAI API, so any OpenAI
// client works unchanged.
//
//	GET    /v1/models
//	POST   /v1/chat/completions (and the other [endpoints])   one request, answered when its turn comes
//	POST   /v1/files            GET /v1/files[/{id}[/content]]   DELETE /v1/files/{id}
//	POST   /v1/batches          GET /v1/batches[/{id}]           POST /v1/batches/{id}/cancel
//	GET    /v1/timeshare/status  what each model is doing (ours)
//	GET    /health               200, no token (ours)
//
// Every /v1 call takes Authorization: Bearer <token>. A single request
// waits for its turn: nothing is streamed (stream: true is refused),
// because an answer may come from the cache or from a model that is still
// loading.
//
// The cache answers to plain HTTP: a request's Cache-Control (no-cache,
// no-store, max-age=N, only-if-cached; see queue.Policy) -- on a batch's
// create, for every line -- and every answer says where it came from in
// Cache-Status (RFC 9211), with Age on one from the cache. A batch's
// output lines carry the same as response.cache_status.
package api

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"mime"
	"net/http"
	"os"
	"strconv"
	"strings"
	"time"

	"gpu-timeshare/internal/auth"
	"gpu-timeshare/internal/batch"
	"gpu-timeshare/internal/config"
	"gpu-timeshare/internal/queue"
	"gpu-timeshare/internal/sched"
)

type Server struct {
	Cfg   *config.Config
	Auth  *auth.Auth
	Q     *queue.Queue
	B     *batch.Store
	Sched *sched.Scheduler
	Logf  func(string, ...any)

	mux *http.ServeMux
}

func (s *Server) logf(format string, a ...any) {
	if s.Logf != nil {
		s.Logf(format, a...)
	}
}

func (s *Server) routes() {
	m := http.NewServeMux()
	m.HandleFunc("GET /health", func(w http.ResponseWriter, r *http.Request) { io.WriteString(w, "ok\n") })
	m.HandleFunc("GET /v1/models", s.authed(s.models))
	m.HandleFunc("GET /v1/models/{model...}", s.authed(s.model))
	for _, e := range s.Cfg.Endpoints {
		m.HandleFunc("POST "+e, s.authed(s.single(e)))
	}
	m.HandleFunc("POST /v1/files", s.authed(s.upload))
	m.HandleFunc("GET /v1/files", s.authed(s.listFiles))
	m.HandleFunc("GET /v1/files/{id}", s.authed(s.getFile))
	m.HandleFunc("GET /v1/files/{id}/content", s.authed(s.fileContent))
	m.HandleFunc("DELETE /v1/files/{id}", s.authed(s.deleteFile))
	m.HandleFunc("POST /v1/batches", s.authed(s.createBatch))
	m.HandleFunc("GET /v1/batches", s.authed(s.listBatches))
	m.HandleFunc("GET /v1/batches/{id}", s.authed(s.getBatch))
	m.HandleFunc("POST /v1/batches/{id}/cancel", s.authed(s.cancelBatch))
	m.HandleFunc("GET /v1/timeshare/status", s.authed(s.status))
	m.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		apiError(w, 404, "invalid_request_error", "unknown_url", fmt.Sprintf("no route %s %s", r.Method, r.URL.Path))
	})
	s.mux = m
}

func (s *Server) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if s.mux == nil {
		s.routes()
	}
	s.mux.ServeHTTP(w, r)
}

// ---- plumbing --------------------------------------------------------------

type handler func(w http.ResponseWriter, r *http.Request, c auth.Client)

func (s *Server) authed(h handler) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		token, ok := strings.CutPrefix(r.Header.Get("Authorization"), "Bearer ")
		if !ok {
			apiError(w, 401, "invalid_request_error", "missing_api_key", "send Authorization: Bearer <token>")
			return
		}
		c, err := s.Auth.Authenticate(strings.TrimSpace(token))
		if err != nil {
			apiError(w, 401, "invalid_request_error", "invalid_api_key", "unknown token")
			return
		}
		h(w, r, c)
	}
}

// apiError writes OpenAI's error shape.
func apiError(w http.ResponseWriter, status int, typ, code, msg string) {
	writeJSON(w, status, map[string]any{"error": map[string]any{
		"message": msg, "type": typ, "param": nil, "code": code}})
}

func paramError(w http.ResponseWriter, msg, param string) {
	writeJSON(w, 400, map[string]any{"error": map[string]any{
		"message": msg, "type": "invalid_request_error", "param": param, "code": nil}})
}

func writeJSON(w http.ResponseWriter, status int, v any) {
	b, err := queue.Marshal(v)
	if err != nil {
		http.Error(w, err.Error(), 500)
		return
	}
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(status)
	w.Write(append(b, '\n'))
}

func (s *Server) internal(w http.ResponseWriter, err error) {
	s.logf("api: %v", err)
	apiError(w, 500, "server_error", "internal_error", "internal error (see the server's log)")
}

// cachePolicy is the request's Cache-Control (all its headers).
func cachePolicy(r *http.Request) queue.Policy {
	return queue.ParseCacheControl(strings.Join(r.Header.Values("Cache-Control"), ","))
}

// ---- models ----------------------------------------------------------------

type modelObject struct {
	ID      string `json:"id"`
	Object  string `json:"object"`
	Created int64  `json:"created"`
	OwnedBy string `json:"owned_by"`
}

func (s *Server) models(w http.ResponseWriter, r *http.Request, c auth.Client) {
	data := []modelObject{}
	for _, n := range s.Cfg.Names() {
		data = append(data, modelObject{ID: n, Object: "model", OwnedBy: "gpu-timeshare"})
	}
	writeJSON(w, 200, map[string]any{"object": "list", "data": data})
}

func (s *Server) model(w http.ResponseWriter, r *http.Request, c auth.Client) {
	name := r.PathValue("model")
	if _, ok := s.Cfg.Models[name]; !ok {
		apiError(w, 404, "invalid_request_error", "model_not_found", fmt.Sprintf("no model %q here", name))
		return
	}
	writeJSON(w, 200, modelObject{ID: name, Object: "model", OwnedBy: "gpu-timeshare"})
}

// ---- one request -----------------------------------------------------------

func (s *Server) single(endpoint string) handler {
	return func(w http.ResponseWriter, r *http.Request, c auth.Client) {
		limit := int64(s.Cfg.Limits.MaxBody)
		if limit <= 0 {
			limit = 1 << 62
		}
		body, err := io.ReadAll(http.MaxBytesReader(w, r.Body, limit))
		var tooBig *http.MaxBytesError
		if errors.As(err, &tooBig) {
			apiError(w, 413, "invalid_request_error", "request_too_large", fmt.Sprintf("the body is over the %d-byte limit", limit))
			return
		}
		if err != nil {
			paramError(w, "reading the body: "+err.Error(), "")
			return
		}
		var head struct {
			Model  string `json:"model"`
			Stream bool   `json:"stream"`
		}
		if err := json.Unmarshal(body, &head); err != nil {
			paramError(w, "the body is not a JSON object: "+err.Error(), "")
			return
		}
		if head.Stream {
			paramError(w, "stream is not available: a request waits for its model's turn", "stream")
			return
		}
		m, ok := s.Cfg.Models[head.Model]
		if !ok {
			apiError(w, 404, "invalid_request_error", "model_not_found", fmt.Sprintf("no model %q here", head.Model))
			return
		}
		key, err := queue.Key(endpoint, m.Identity(), body)
		if err != nil {
			paramError(w, "the body is not JSON: "+err.Error(), "")
			return
		}
		pol := cachePolicy(r)
		pol.Read, pol.Write = pol.Read && m.Caches(s.Cfg), pol.Write && m.Caches(s.Cfg)
		id, hit, err := s.Q.Insert(s.Q.DB, queue.New{Client: c.Name, Model: m.Name, Endpoint: endpoint,
			Body: body, Key: key, ReadCache: pol.Read, Write: pol.Write, MaxAge: pol.MaxAge, OnlyIfCached: pol.OnlyIfCached})
		if err != nil {
			s.internal(w, err)
			return
		}
		defer s.Q.Forget(id)
		if !hit && pol.OnlyIfCached {
			w.Header().Set("Cache-Status", "gpu-timeshare; fwd=miss; detail=only-if-cached")
			apiError(w, 504, "invalid_request_error", "not_cached",
				"only-if-cached: no answer to this question is in the cache")
			return
		}
		if !hit {
			wait := s.Sched.Waiter(id)
			s.Sched.Wake()
			res, err := s.Q.Result(id)
			if err != nil {
				s.Sched.Unwait(id)
				s.internal(w, err)
				return
			}
			if res.State == "queued" {
				select {
				case <-wait:
				case <-r.Context().Done():
					s.Sched.Unwait(id)
					return // the caller left; its row goes, an answer in flight is still cached
				}
			} else {
				s.Sched.Unwait(id)
			}
		}
		res, err := s.Q.Result(id)
		if err != nil {
			s.internal(w, err)
			return
		}
		switch res.State {
		case "done":
			w.Header().Set("Cache-Status", queue.CacheStatus(pol, res))
			if age := queue.Age(res, time.Now()); age != "" {
				w.Header().Set("Age", age)
			}
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(res.Status)
			w.Write(queue.Present(m, m.Name, res.Body))
		case "failed":
			status := 502
			switch res.ErrorCode {
			case "model_unavailable":
				status = 503
			case "invalid_request":
				status = 400
			}
			apiError(w, status, "server_error", res.ErrorCode, res.Error)
		default:
			s.internal(w, fmt.Errorf("request %d woke as %q", id, res.State))
		}
	}
}

// ---- files -----------------------------------------------------------------

func (s *Server) upload(w http.ResponseWriter, r *http.Request, c auth.Client) {
	if limit := int64(s.Cfg.Limits.MaxFile); limit > 0 {
		r.Body = http.MaxBytesReader(w, r.Body, limit+1<<20) // the multipart framing
	}
	mr, err := r.MultipartReader()
	if err != nil {
		paramError(w, "want multipart/form-data with file and purpose", "file")
		return
	}
	purpose := ""
	var saved *batch.File
	for {
		part, err := mr.NextPart()
		if err == io.EOF {
			break
		}
		if err != nil {
			paramError(w, "reading the upload: "+err.Error(), "file")
			return
		}
		switch part.FormName() {
		case "purpose":
			b, _ := io.ReadAll(io.LimitReader(part, 256))
			purpose = strings.TrimSpace(string(b))
		case "file":
			if saved != nil {
				paramError(w, "one file per upload", "file")
				return
			}
			name := part.FileName()
			if name == "" {
				name = "upload.jsonl"
			}
			f, err := s.B.SaveFile(c.Name, "batch", name, part)
			if err != nil {
				paramError(w, "storing the file: "+err.Error(), "file")
				return
			}
			saved = &f
		}
		part.Close()
	}
	if saved == nil {
		paramError(w, "no file in the upload", "file")
		return
	}
	if purpose != "batch" {
		s.B.DeleteFile(saved.ID, c.Name, false)
		paramError(w, fmt.Sprintf("purpose %q: only \"batch\" files are kept here", purpose), "purpose")
		return
	}
	writeJSON(w, 200, saved)
}

func (s *Server) listFiles(w http.ResponseWriter, r *http.Request, c auth.Client) {
	fs, err := s.B.ListFiles(c.Name, c.Admin, r.URL.Query().Get("purpose"))
	if err != nil {
		s.internal(w, err)
		return
	}
	if fs == nil {
		fs = []batch.File{}
	}
	writeJSON(w, 200, map[string]any{"object": "list", "data": fs, "has_more": false})
}

func (s *Server) findFile(w http.ResponseWriter, r *http.Request, c auth.Client) (batch.File, bool) {
	f, err := s.B.GetFile(r.PathValue("id"), c.Name, c.Admin)
	if errors.Is(err, batch.ErrNotFound) {
		apiError(w, 404, "invalid_request_error", "file_not_found", fmt.Sprintf("no file %q", r.PathValue("id")))
		return f, false
	}
	if err != nil {
		s.internal(w, err)
		return f, false
	}
	return f, true
}

func (s *Server) getFile(w http.ResponseWriter, r *http.Request, c auth.Client) {
	if f, ok := s.findFile(w, r, c); ok {
		writeJSON(w, 200, f)
	}
}

func (s *Server) fileContent(w http.ResponseWriter, r *http.Request, c auth.Client) {
	f, ok := s.findFile(w, r, c)
	if !ok {
		return
	}
	fh, err := os.Open(queue.FilePath(s.Cfg.FilesDir(), f.ID))
	if err != nil {
		s.internal(w, err)
		return
	}
	defer fh.Close()
	w.Header().Set("Content-Type", "application/octet-stream")
	w.Header().Set("Content-Length", strconv.FormatInt(f.Bytes, 10))
	w.Header().Set("Content-Disposition", mime.FormatMediaType("attachment", map[string]string{"filename": f.Filename}))
	io.Copy(w, fh)
}

func (s *Server) deleteFile(w http.ResponseWriter, r *http.Request, c auth.Client) {
	id := r.PathValue("id")
	err := s.B.DeleteFile(id, c.Name, c.Admin)
	switch {
	case errors.Is(err, batch.ErrNotFound):
		apiError(w, 404, "invalid_request_error", "file_not_found", fmt.Sprintf("no file %q", id))
	case errors.Is(err, batch.ErrInUse):
		apiError(w, 409, "invalid_request_error", "file_in_use", err.Error())
	case err != nil:
		s.internal(w, err)
	default:
		writeJSON(w, 200, map[string]any{"id": id, "object": "file", "deleted": true})
	}
}

// ---- batches ---------------------------------------------------------------

func (s *Server) createBatch(w http.ResponseWriter, r *http.Request, c auth.Client) {
	var req batch.Create
	if err := json.NewDecoder(io.LimitReader(r.Body, 1<<20)).Decode(&req); err != nil {
		paramError(w, "the body is not a JSON object: "+err.Error(), "")
		return
	}
	b, hits, err := s.B.New(c.Name, c.Admin, req, cachePolicy(r))
	var bad *batch.BadRequest
	if errors.As(err, &bad) {
		paramError(w, bad.Msg, bad.Param)
		return
	}
	if err != nil {
		s.internal(w, err)
		return
	}
	if b.Status == "failed" {
		s.logf("batch %s (%s): failed validation", b.ID, c.Name)
	} else {
		s.logf("batch %s (%s): %d request(s), %d from the cache", b.ID, c.Name, b.RequestCounts.Total, hits)
	}
	s.Sched.Wake()
	if got, err := s.B.Get(b.ID, c.Name, c.Admin); err == nil {
		b = got
	}
	writeJSON(w, 200, b)
}

func (s *Server) listBatches(w http.ResponseWriter, r *http.Request, c auth.Client) {
	limit, _ := strconv.Atoi(r.URL.Query().Get("limit"))
	bs, more, err := s.B.List(c.Name, c.Admin, r.URL.Query().Get("after"), limit)
	if err != nil {
		s.internal(w, err)
		return
	}
	out := map[string]any{"object": "list", "data": bs, "has_more": more, "first_id": nil, "last_id": nil}
	if len(bs) == 0 {
		out["data"] = []batch.Batch{}
	} else {
		out["first_id"], out["last_id"] = bs[0].ID, bs[len(bs)-1].ID
	}
	writeJSON(w, 200, out)
}

func (s *Server) batchResult(w http.ResponseWriter, id string, b batch.Batch, err error) {
	if errors.Is(err, batch.ErrNotFound) {
		apiError(w, 404, "invalid_request_error", "batch_not_found", fmt.Sprintf("no batch %q", id))
		return
	}
	if err != nil {
		s.internal(w, err)
		return
	}
	writeJSON(w, 200, b)
}

func (s *Server) getBatch(w http.ResponseWriter, r *http.Request, c auth.Client) {
	id := r.PathValue("id")
	b, err := s.B.Get(id, c.Name, c.Admin)
	s.batchResult(w, id, b, err)
}

func (s *Server) cancelBatch(w http.ResponseWriter, r *http.Request, c auth.Client) {
	id := r.PathValue("id")
	b, err := s.B.Cancel(id, c.Name, c.Admin)
	if err == nil {
		s.Sched.Wake()
	}
	s.batchResult(w, id, b, err)
}

// ---- ours ------------------------------------------------------------------

func (s *Server) status(w http.ResponseWriter, r *http.Request, c auth.Client) {
	st, err := s.Sched.Status()
	if err != nil {
		s.internal(w, err)
		return
	}
	writeJSON(w, 200, map[string]any{"object": "timeshare.status", "models": st})
}
