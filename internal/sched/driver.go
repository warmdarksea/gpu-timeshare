package sched

import (
	"context"
	"encoding/json"
	"fmt"
	"sort"
	"strings"
	"sync"
	"time"

	"gpu-timeshare/internal/batch"
	"gpu-timeshare/internal/config"
	"gpu-timeshare/internal/queue"
	"gpu-timeshare/internal/upstream"
)

// Scheduler applies Decide to the model servers and feeds them requests.
type Scheduler struct {
	Cfg       *config.Config
	Q         *queue.Queue
	B         *batch.Store
	NewServer func(*config.Model) (upstream.Server, error)
	Tick      time.Duration
	Logf      func(format string, a ...any)

	mu      sync.Mutex
	slots   map[string]*slot
	running map[int64]run   // request id -> what it is
	keys    map[string]bool // cache keys being answered
	cursor  map[string]string
	waiters map[int64]chan struct{}
	wake    chan struct{}
	ready   chan struct{} // closed once Run has set up
	once    sync.Once
}

type run struct{ batch, key string }

type slot struct {
	model      *config.Model
	server     upstream.Server
	state      State
	upSince    time.Time // when it last finished loading (Decide's LoadedAt)
	busyAt     time.Time
	inflight   int
	startFails int
	brokenAt   time.Time // zero: not broken
	lastError  string
}

func (s *Scheduler) logf(format string, a ...any) {
	if s.Logf != nil {
		s.Logf(format, a...)
	}
}

func (s *Scheduler) init() {
	s.once.Do(func() {
		s.slots, s.running, s.keys = map[string]*slot{}, map[int64]run{}, map[string]bool{}
		s.cursor, s.waiters = map[string]string{}, map[int64]chan struct{}{}
		s.wake, s.ready = make(chan struct{}, 1), make(chan struct{})
		for _, n := range s.Cfg.Names() {
			s.slots[n] = &slot{model: s.Cfg.Models[n]}
		}
		if s.Tick == 0 {
			s.Tick = 200 * time.Millisecond
		}
	})
}

// Wake asks for a round now (new work arrived).
func (s *Scheduler) Wake() {
	s.init()
	select {
	case s.wake <- struct{}{}:
	default:
	}
}

// Waiter is closed when the request is no longer queued or running.
// Register it before checking the request's state, so no answer is missed.
func (s *Scheduler) Waiter(id int64) <-chan struct{} {
	s.init()
	s.mu.Lock()
	defer s.mu.Unlock()
	ch, ok := s.waiters[id]
	if !ok {
		ch = make(chan struct{})
		s.waiters[id] = ch
	}
	return ch
}

// Unwait drops a waiter nobody listens to any more.
func (s *Scheduler) Unwait(id int64) {
	s.mu.Lock()
	delete(s.waiters, id)
	s.mu.Unlock()
}

func (s *Scheduler) notify(ids ...int64) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.notifyLocked(ids...)
}

func (s *Scheduler) notifyLocked(ids ...int64) {
	for _, id := range ids {
		if ch, ok := s.waiters[id]; ok {
			close(ch)
			delete(s.waiters, id)
		}
	}
}

// Run schedules until ctx ends, then stops every model.
func (s *Scheduler) Run(ctx context.Context) error {
	s.init()
	close(s.ready)
	defer s.stopAll()
	tick := time.NewTicker(s.Tick)
	defer tick.Stop()
	var lastUpkeep, lastCache, lastFiles time.Time
	for {
		if err := s.round(ctx); err != nil {
			return err
		}
		now := time.Now()
		if now.Sub(lastUpkeep) >= time.Second {
			lastUpkeep = now
			if err := s.upkeep(now); err != nil {
				s.logf("upkeep: %v", err)
			}
		}
		if now.Sub(lastCache) >= time.Minute {
			lastCache = now
			e := queue.Expiry{MaxAge: s.Cfg.Cache.MaxAge.Duration, MaxUnused: s.Cfg.Cache.MaxUnused.Duration,
				MaxSize: int64(s.Cfg.Cache.MaxSize)}
			if n, err := s.Q.Expire(e, now); err != nil {
				s.logf("cache expiry: %v", err)
			} else if n > 0 {
				s.logf("cache: %d answer(s) expired", n)
			}
		}
		if now.Sub(lastFiles) >= time.Hour {
			lastFiles = now
			if n, err := s.B.ExpireFiles(now); err != nil {
				s.logf("file expiry: %v", err)
			} else if n > 0 {
				s.logf("files: %d past retention deleted", n)
			}
		}
		select {
		case <-ctx.Done():
			return nil
		case <-tick.C:
		case <-s.wake:
		}
	}
}

// round is one pass: decide, apply, dispatch.
func (s *Scheduler) round(ctx context.Context) error {
	counts, err := s.Q.Counts()
	if err != nil {
		return err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	now := time.Now()
	brokenFor := s.Cfg.Scheduler.BrokenFor.Duration

	var models []Model
	var refuse []string
	for _, name := range s.Cfg.Names() {
		sl := s.slots[name]
		if (sl.state == Up || sl.state == Draining) && !sl.server.Alive() {
			// a server that dies at work is as broken as one that won't
			// start: restarting it only burns attempts
			if now.Sub(sl.upSince) > 10*time.Minute {
				sl.startFails = 0 // it worked for a while: a fresh failure, not a pattern
			}
			sl.state, sl.server = Down, nil
			s.failedStart(name, sl, "the server exited")
		}
		if !sl.brokenAt.IsZero() && now.Sub(sl.brokenAt) >= brokenFor {
			sl.brokenAt, sl.startFails = time.Time{}, 0
			s.logf("%s: trying it again", name)
		}
		ready := counts[name] - sl.inflight
		if ready < 0 {
			ready = 0
		}
		if !sl.brokenAt.IsZero() {
			if ready > 0 {
				refuse = append(refuse, name)
			}
			ready = 0
		}
		if ready > 0 || sl.inflight > 0 || sl.state == Starting {
			sl.busyAt = now
		}
		models = append(models, Model{Name: name, State: sl.state,
			Inflight: sl.inflight, Ready: ready, BusyAt: sl.busyAt, LoadedAt: sl.upSince})
	}
	for _, name := range refuse {
		ids, err := s.Q.FailQueued(name, "model_unavailable",
			fmt.Sprintf("model %s failed to start: %s", name, s.slots[name].lastError))
		if err != nil {
			return err
		}
		// a running request keeps its row queued; it isn't failed here
		s.notifyLocked(ids...)
	}

	pol := Policy{MaxTimeslice: s.Cfg.Scheduler.MaxTimeslice.Duration, Idle: s.Cfg.Scheduler.Idle.Duration}
	for _, a := range Decide(models, now, pol) {
		sl := s.slots[a.Model]
		switch a.Kind {
		case Start:
			s.start(ctx, a.Model, sl)
		case Stop:
			switch {
			case sl.state == Draining:
				s.logf("%s: drained: stopping", a.Model)
			case pol.Idle > 0 && now.Sub(sl.busyAt) >= pol.Idle:
				s.logf("%s: idle for %s: stopping", a.Model, now.Sub(sl.busyAt).Round(time.Second))
			default:
				s.logf("%s: nothing to do, and a model waits: stopping", a.Model)
			}
			srv := sl.server
			sl.state, sl.server = Down, nil
			go srv.Stop()
		case Drain:
			s.logf("%s: it has had the card for %s, and a model waits: draining", a.Model, now.Sub(sl.upSince).Round(time.Second))
			sl.state = Draining
		}
	}
	for _, name := range s.Cfg.Names() {
		if sl := s.slots[name]; sl.state == Up {
			if err := s.dispatch(ctx, name, sl); err != nil {
				return err
			}
		}
	}
	return nil
}

func (s *Scheduler) failedStart(name string, sl *slot, why string) {
	sl.startFails++
	sl.lastError = why
	s.logf("%s: %s (%d)", name, why, sl.startFails)
	if sl.startFails >= 2 {
		sl.brokenAt = time.Now()
		s.logf("%s: refusing its requests for %s", name, s.Cfg.Scheduler.BrokenFor.Duration)
	}
}

func (s *Scheduler) start(ctx context.Context, name string, sl *slot) {
	srv, err := s.NewServer(sl.model)
	if err != nil {
		s.failedStart(name, sl, err.Error())
		sl.startFails = 2
		sl.brokenAt = time.Now()
		return
	}
	sl.state, sl.server = Starting, srv
	s.logf("%s: starting", name)
	go func() {
		t := time.Now()
		err := srv.Start(ctx)
		s.mu.Lock()
		defer s.mu.Unlock()
		if sl.server != srv { // stopped meanwhile
			return
		}
		if err != nil {
			sl.state, sl.server = Down, nil
			s.failedStart(name, sl, "failed to start: "+err.Error())
			return
		}
		sl.state, sl.upSince, sl.busyAt = Up, time.Now(), time.Now()
		s.logf("%s: up after %s (as %q)", name, time.Since(t).Round(time.Millisecond), srv.UpstreamModel())
		s.Wake()
	}()
}

// dispatch sends queued requests up to the model's concurrency, taking
// turns between clients. A question already being answered isn't asked
// again: its twin waits and gets the same answer.
func (s *Scheduler) dispatch(ctx context.Context, name string, sl *slot) error {
	free := sl.model.Concurrency - sl.inflight
	if free <= 0 {
		return nil
	}
	byClient, err := s.Q.Queued(name, free+sl.inflight)
	if err != nil {
		return err
	}
	for c, rs := range byClient {
		var keep []queue.Request
		for _, r := range rs {
			if _, busy := s.running[r.ID]; !busy && !s.keys[r.Key] {
				keep = append(keep, r)
			}
		}
		byClient[c] = keep
	}
	picked, last := RoundRobin(byClient, s.cursor[name], free)
	if last != "" {
		s.cursor[name] = last
	}
	for _, r := range picked {
		s.running[r.ID] = run{batch: r.BatchID, key: r.Key}
		s.keys[r.Key] = true
		sl.inflight++
		go s.execute(ctx, sl, sl.server, r)
	}
	return nil
}

// RoundRobin picks up to n requests, one per client in turn, starting
// after the client served last; each client's own come in the order given.
// Two of the picks never share a cache key.
func RoundRobin(byClient map[string][]queue.Request, after string, n int) ([]queue.Request, string) {
	clients := make([]string, 0, len(byClient))
	for c, rs := range byClient {
		if len(rs) > 0 {
			clients = append(clients, c)
		}
	}
	if len(clients) == 0 {
		return nil, ""
	}
	sort.Strings(clients)
	start := sort.SearchStrings(clients, after)
	if start < len(clients) && clients[start] == after {
		start++
	}
	var picked []queue.Request
	keys := map[string]bool{}
	next := map[string]int{}
	last := ""
	for len(picked) < n {
		progressed := false
		for i := range clients {
			if len(picked) == n {
				break
			}
			c := clients[(start+i)%len(clients)]
			for next[c] < len(byClient[c]) {
				r := byClient[c][next[c]]
				next[c]++
				if keys[r.Key] {
					continue
				}
				keys[r.Key] = true
				picked = append(picked, r)
				last, progressed = c, true
				break
			}
		}
		if !progressed {
			break
		}
	}
	return picked, last
}

// withModel replaces a body's "model" with the upstream's name.
func withModel(body []byte, model string) ([]byte, error) {
	var obj map[string]json.RawMessage
	if err := json.Unmarshal(body, &obj); err != nil {
		return nil, err
	}
	obj["model"], _ = json.Marshal(model)
	return queue.Marshal(obj)
}

func (s *Scheduler) execute(ctx context.Context, sl *slot, srv upstream.Server, r queue.Request) {
	defer s.Wake()
	var done []int64
	defer func() {
		s.mu.Lock()
		sl.inflight--
		delete(s.running, r.ID)
		delete(s.keys, r.Key)
		s.notifyLocked(done...)
		s.mu.Unlock()
	}()
	max := s.Cfg.Scheduler.MaxAttempts
	retry := func(msg string) {
		failed, err := s.Q.Retry(r.ID, msg, max)
		if err != nil {
			s.logf("%s #%d: %v", r.Model, r.ID, err)
		}
		if failed {
			s.logf("%s #%d: failed: %s", r.Model, r.ID, msg)
			done = append(done, r.ID)
		}
	}
	body, err := s.Q.Body(r.ID)
	if err == nil {
		body, err = withModel(body, srv.UpstreamModel())
	}
	if err != nil {
		s.Q.Fail(r.ID, "invalid_request", "reading the request: "+err.Error())
		done = append(done, r.ID)
		return
	}
	t := time.Now()
	status, reply, err := srv.Do(ctx, r.Endpoint, body)
	elapsed := time.Since(t)
	if err != nil {
		if ctx.Err() != nil {
			return // shutting down: it stays queued for next time
		}
		retry(err.Error())
		return
	}
	if status >= 500 || status == 429 {
		retry(fmt.Sprintf("the model answered %d: %s", status, excerpt(reply)))
		return
	}
	ok := status >= 200 && status < 300
	also, err := s.Q.Done(r.ID, status, reply, r.Key, ok)
	if err != nil {
		s.logf("%s #%d: %v", r.Model, r.ID, err)
		return
	}
	done = append(append(done, r.ID), also...)
	if ok && r.Write {
		if err := s.Q.Remember(r.Key, r.Model, sl.model.Identity(), r.Endpoint, reply, elapsed); err != nil {
			s.logf("%s #%d: caching: %v", r.Model, r.ID, err)
		}
	}
}

func excerpt(b []byte) string {
	s := strings.TrimSpace(string(b))
	if len(s) > 300 {
		s = s[:300] + "..."
	}
	return s
}

// upkeep ends batches: expired ones lose their queue, and any with nothing
// left queued or running get their result files.
func (s *Scheduler) upkeep(now time.Time) error {
	expired, err := s.B.Expire(now)
	if err != nil {
		return err
	}
	for _, id := range expired {
		s.logf("batch %s: expired", id)
	}
	s.mu.Lock()
	busy := map[string]bool{}
	for _, r := range s.running {
		if r.batch != "" {
			busy[r.batch] = true
		}
	}
	s.mu.Unlock()
	ids, err := s.B.Finished(func(id string) bool { return busy[id] })
	if err != nil {
		return err
	}
	for _, id := range ids {
		if err := s.B.Finalize(id, func(model string, body []byte) []byte {
			return queue.Present(s.Cfg.Models[model], model, body)
		}); err != nil {
			s.logf("batch %s: writing its results: %v", id, err)
			continue
		}
		s.logf("batch %s: finished", id)
	}
	return nil
}

func (s *Scheduler) stopAll() {
	s.mu.Lock()
	var ss []upstream.Server
	for _, sl := range s.slots {
		if sl.server != nil {
			ss = append(ss, sl.server)
			sl.server, sl.state = nil, Down
		}
	}
	s.mu.Unlock()
	var wg sync.WaitGroup
	for _, srv := range ss {
		wg.Add(1)
		go func() { defer wg.Done(); srv.Stop() }()
	}
	wg.Wait()
}

// Status is one model's state, for /v1/timeshare/status.
type Status struct {
	Model    string `json:"model"`
	State    string `json:"state"`
	UpSince  *int64 `json:"up_since"`
	Inflight int    `json:"in_flight"`
	Queued   int    `json:"queued"`
	Broken   string `json:"unavailable,omitempty"`
}

func (s *Scheduler) Status() ([]Status, error) {
	s.init()
	counts, err := s.Q.Counts()
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	var out []Status
	for _, n := range s.Cfg.Names() {
		sl := s.slots[n]
		st := Status{Model: n, State: sl.state.String(), Inflight: sl.inflight,
			Queued: counts[n] - sl.inflight}
		if sl.state == Up || sl.state == Draining {
			t := sl.upSince.Unix()
			st.UpSince = &t
		}
		if !sl.brokenAt.IsZero() {
			st.Broken = sl.lastError
		}
		out = append(out, st)
	}
	return out, nil
}
