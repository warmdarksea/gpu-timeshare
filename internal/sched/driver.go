package sched

import (
	"context"
	"encoding/json"
	"fmt"
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
	NewServer func(m *config.Model, gpu string) (upstream.Server, error)
	Tick      time.Duration
	Logf      func(format string, a ...any)

	mu      sync.Mutex
	cards   []*card            // one per GPU
	health  map[string]*health // by model
	lines   Lines              // who has waited longest (policy.go)
	running map[int64]run      // request id -> what it is
	keys    map[string]bool    // cache keys being answered
	cursor  map[string]string  // by model: the tenant served last
	waiters map[int64]chan struct{}
	wake    chan struct{}
	ready   chan struct{} // closed once Run has set up
	once    sync.Once
}

type run struct{ batch, key, client, model, card string }

// card is one GPU and what is on it.
type card struct {
	id       string // Decide's name for it
	gpu      string // the config's
	model    *config.Model
	server   upstream.Server
	state    State
	owner    string        // the tenant whose turn it is, or will be once it has drained
	next     string        // the model it drains for, or has drained for (Decide's Next)
	turnAt   time.Time     // when the turn began (Decide's TurnAt)
	upSince  time.Time     // when the model finished loading
	load     time.Duration // how long that took
	busyAt   time.Time
	inflight int
}

// health is a model's record of failing.
type health struct {
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
		s.health, s.running, s.keys = map[string]*health{}, map[int64]run{}, map[string]bool{}
		s.cursor, s.waiters = map[string]string{}, map[int64]chan struct{}{}
		s.wake, s.ready = make(chan struct{}, 1), make(chan struct{})
		for _, n := range s.Cfg.Names() {
			s.health[n] = &health{}
		}
		for i, g := range s.Cfg.GPUList() {
			s.cards = append(s.cards, &card{id: fmt.Sprint("card", i), gpu: g})
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
	queued, err := s.Q.Flows()
	if err != nil {
		return err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	now := time.Now()
	brokenFor := s.Cfg.Scheduler.BrokenFor.Duration

	for _, c := range s.cards {
		if (c.state == Up || c.state == Draining) && !c.server.Alive() {
			// a server that dies at work is as broken as one that won't
			// start: restarting it only burns attempts
			h := s.health[c.model.Name]
			if now.Sub(c.upSince) > 10*time.Minute {
				h.startFails = 0 // it worked for a while: a fresh failure, not a pattern
			}
			s.failed(c, "the server exited")
		}
	}
	// the flows: what is queued and not in flight, less what a broken model is refused
	inflight := map[[2]string]int{} // by tenant and model
	for _, r := range s.running {
		inflight[[2]string{r.client, r.model}]++
	}
	var flows []Flow
	work := map[string]int{} // by model
	var refuse []string
	for _, name := range s.Cfg.Names() {
		h := s.health[name]
		if !h.brokenAt.IsZero() && now.Sub(h.brokenAt) >= brokenFor {
			h.brokenAt, h.startFails = time.Time{}, 0
			s.logf("%s: trying it again", name)
		}
	}
	for _, f := range queued {
		h := s.health[f.Model]
		if h == nil {
			continue // a model the config no longer has
		}
		n := f.Queued - inflight[[2]string{f.Client, f.Model}]
		if n <= 0 {
			continue
		}
		if !h.brokenAt.IsZero() {
			if len(refuse) == 0 || refuse[len(refuse)-1] != f.Model {
				refuse = append(refuse, f.Model)
			}
			continue
		}
		flows = append(flows, Flow{Tenant: f.Client, Model: f.Model, Queued: n, Oldest: f.Oldest})
		work[f.Model] += n
	}
	for _, name := range refuse {
		ids, err := s.Q.FailQueued(name, "model_unavailable",
			fmt.Sprintf("model %s failed to start: %s", name, s.health[name].lastError))
		if err != nil {
			return err
		}
		// a running request keeps its row queued; it isn't failed here
		s.notifyLocked(ids...)
	}
	var cards []Card
	byID := map[string]*card{}
	for _, c := range s.cards {
		v := Card{ID: c.id, State: c.state, Owner: c.owner, Next: c.next, Inflight: c.inflight, TurnAt: c.turnAt, Load: c.load}
		if c.model != nil {
			v.Model = c.model.Name
			if c.inflight > 0 || work[v.Model] > 0 || c.state == Starting {
				c.busyAt = now
			}
		}
		v.BusyAt = c.busyAt
		cards, byID[c.id] = append(cards, v), c
	}
	slots := map[string]int{}
	for name, m := range s.Cfg.Models {
		slots[name] = m.Concurrency
	}

	pol := Policy{MaxTimeslice: s.Cfg.Scheduler.MaxTimeslice.Duration, LoadRatio: s.Cfg.Scheduler.LoadRatio,
		Idle: s.Cfg.Scheduler.Idle.Duration}
	acts, lines := DecideLean(cards, flows, slots, s.lines, now, pol)
	s.lines = lines
	for _, a := range acts {
		c := byID[a.Card]
		switch a.Kind {
		case Start:
			s.start(ctx, c, s.Cfg.Models[a.Model], a.Tenant)
		case Stop:
			if c.server == nil {
				continue // its start failed earlier in this round
			}
			switch {
			case c.state == Draining:
				s.logf("%s: drained: stopping", s.on(c, a.Model))
			case work[a.Model] == 0 && pol.Idle > 0 && now.Sub(c.busyAt) >= pol.Idle:
				s.logf("%s: idle for %s: stopping", s.on(c, a.Model), now.Sub(c.busyAt).Round(time.Second))
			default:
				s.logf("%s: nothing to do, and a model waits: stopping", s.on(c, a.Model))
			}
			srv := c.server
			if c.state == Draining { // it stays its next tenant's: Decide starts their model on it
				*c = card{id: c.id, gpu: c.gpu, owner: c.owner, next: c.next}
			} else {
				*c = card{id: c.id, gpu: c.gpu}
			}
			go srv.Stop()
		case Drain:
			if c.state != Up {
				continue
			}
			s.logf("%s: %s's turn is %s old: draining, for %s (%s's turn)",
				s.on(c, a.Model), c.owner, now.Sub(c.turnAt).Round(100*time.Millisecond), a.For, a.Tenant)
			c.state, c.owner, c.next = Draining, a.Tenant, a.For
		case Pass:
			s.logf("%s: the turn passes from %s to %s", s.on(c, a.Model), c.owner, a.Tenant)
			c.owner, c.turnAt = a.Tenant, now
		}
	}
	for _, c := range s.cards {
		if c.state == Up {
			if err := s.dispatch(ctx, c); err != nil {
				return err
			}
		}
	}
	return nil
}

// failed is the end of a turn nobody decided: a load that failed, or a
// server that died. The card is free; twice and the model is refused for
// a while.
func (s *Scheduler) failed(c *card, why string) {
	name := c.model.Name
	h := s.health[name]
	h.startFails++
	h.lastError = why
	s.logf("%s: %s (%d)", s.on(c, name), why, h.startFails)
	if h.startFails >= 2 {
		h.brokenAt = time.Now()
		s.logf("%s: refusing its requests for %s", name, s.Cfg.Scheduler.BrokenFor.Duration)
	}
	if c.state == Draining {
		// its turn ended when it began to drain, and the next one is already
		// somebody's: the card is theirs, as if it had drained
		*c = card{id: c.id, gpu: c.gpu, owner: c.owner, next: c.next}
		return
	}
	s.lines.Ended(c.owner, name)
	*c = card{id: c.id, gpu: c.gpu}
}

func (s *Scheduler) start(ctx context.Context, c *card, m *config.Model, tenant string) {
	c.model, c.owner, c.state, c.next = m, tenant, Starting, ""

	srv, err := s.NewServer(m, c.gpu)
	if err != nil {
		s.health[m.Name].startFails = 2 // nothing to retry
		s.failed(c, err.Error())
		return
	}
	c.server = srv
	s.logf("%s: starting (%s's turn)", s.on(c, m.Name), tenant)
	go func() {
		t := time.Now()
		err := srv.Start(ctx)
		s.mu.Lock()
		defer s.mu.Unlock()
		if c.server != srv { // stopped meanwhile
			return
		}
		if err != nil {
			s.failed(c, "failed to start: "+err.Error())
			s.Wake()
			return
		}
		now := time.Now()
		c.state, c.upSince, c.turnAt, c.busyAt, c.load = Up, now, now, now, now.Sub(t)
		s.logf("%s: up after %s (as %q)", s.on(c, m.Name), c.load.Round(time.Millisecond), srv.UpstreamModel())
		s.Wake()
	}()
}

// dispatch sends queued requests up to the model's concurrency, by
// RoundRobin (policy.go). A question already being answered isn't asked
// again: its twin waits and gets the same answer.
func (s *Scheduler) dispatch(ctx context.Context, c *card) error {
	name := c.model.Name
	free := c.model.Concurrency - c.inflight
	if free <= 0 {
		return nil
	}
	inflight := map[string]int{} // by tenant, on every card that has this model
	for _, r := range s.running {
		if r.model == name {
			inflight[r.client]++
		}
	}
	// enough per client that the ones in flight (still queued in the db) can't hide the rest
	busy := 0
	for _, n := range inflight {
		busy += n
	}
	byClient, err := s.Q.Queued(name, free+busy)
	if err != nil {
		return err
	}
	for cl, rs := range byClient {
		var keep []queue.Request
		for _, r := range rs {
			if _, busy := s.running[r.ID]; !busy && !s.keys[r.Key] {
				keep = append(keep, r)
			}
		}
		byClient[cl] = keep
	}
	own := Owner{Tenant: c.owner, Slots: c.model.Concurrency}
	for _, r := range s.running {
		if r.card == c.id && r.client == c.owner {
			own.Held++
		}
	}
	picked, last := RoundRobinLean(byClient, func(r queue.Request) string { return r.Key }, inflight, own, s.cursor[name], free)
	if last != "" {
		s.cursor[name] = last
	}
	for _, r := range picked {
		s.running[r.ID] = run{batch: r.BatchID, key: r.Key, client: r.Client, model: name, card: c.id}

		s.keys[r.Key] = true
		c.inflight++
		go s.execute(ctx, c, c.server, r)
	}
	return nil
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

func (s *Scheduler) execute(ctx context.Context, c *card, srv upstream.Server, r queue.Request) {
	defer s.Wake()
	var done []int64
	defer func() {
		s.mu.Lock()
		if c.server == srv {
			c.inflight--
		}
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
		if err := s.Q.Remember(r.Key, r.Model, s.Cfg.Models[r.Model].Identity(), r.Endpoint, reply, elapsed); err != nil {
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
	for _, c := range s.cards {
		if c.server != nil {
			ss = append(ss, c.server)
			*c = card{id: c.id, gpu: c.gpu}
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
	Model    string   `json:"model"`
	State    string   `json:"state"` // of the card it is furthest along on
	Cards    []string `json:"cards"` // the cards it is on
	UpSince  *int64   `json:"up_since"`
	Inflight int      `json:"in_flight"`
	Queued   int      `json:"queued"`
	Broken   string   `json:"unavailable,omitempty"`
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
		st := Status{Model: n, State: Down.String(), Cards: []string{}}
		best := Down
		for _, c := range s.cards {
			if c.model == nil || c.model.Name != n {
				continue
			}
			st.Cards = append(st.Cards, c.id)
			st.Inflight += c.inflight
			// up, then draining, then starting
			if rank := map[State]int{Up: 3, Draining: 2, Starting: 1}; rank[c.state] > rank[best] {
				best = c.state
			}
			if c.state == Up || c.state == Draining {
				if t := c.upSince.Unix(); st.UpSince == nil || t < *st.UpSince {
					st.UpSince = &t
				}
			}
		}
		st.State = best.String()
		st.Queued = counts[n] - st.Inflight
		if h := s.health[n]; !h.brokenAt.IsZero() {
			st.Broken = h.lastError
		}
		out = append(out, st)
	}
	return out, nil
}

// on names a model on a card, for the log: just the model when there is
// only the one card.
func (s *Scheduler) on(c *card, model string) string {
	if len(s.cards) == 1 {
		return model
	}
	return model + " on " + c.id
}
