package sched

import (
	"fmt"
	"io"
	"math/rand"
	"reflect"
	"sort"
	"testing"
	"time"
)

var t0 = time.Date(2026, 11, 10, 12, 0, 0, 0, time.UTC)

var pol = Policy{MaxTimeslice: 2 * time.Hour}

func ago(d time.Duration) time.Time { return t0.Add(-d) }

// world builds Decide's arguments: flows as "tenant/model" (in the order
// they joined), every model with 4 slots
func decide(p Policy, cards []Card, lines *Lines, flows ...string) []Action {
	var fs []Flow
	slots := map[string]int{}
	for i, f := range flows {
		var t, m string
		for j := range f {
			if f[j] == '/' {
				t, m = f[:j], f[j+1:]
			}
		}
		fs = append(fs, Flow{Tenant: t, Model: m, Queued: 100, Oldest: int64(i + 1)})
		slots[m] = 4
	}
	for _, c := range cards {
		slots[c.Model] = 4
	}
	acts, l := Decide(cards, fs, slots, *lines, t0, p)
	*lines = l
	return acts
}

func want(t *testing.T, got []Action, w ...Action) {
	t.Helper()
	if len(w) == 0 {
		w = nil
	}
	if !reflect.DeepEqual(got, w) {
		t.Errorf("got %v, want %v", got, w)
	}
}

func up(id, model, owner string, turn time.Duration) Card {
	return Card{ID: id, State: Up, Model: model, Owner: owner, Inflight: 4, TurnAt: ago(turn), BusyAt: t0}
}

// [Start]: a free card goes to whoever is first in line, for its first model
func TestStart(t *testing.T) {
	var l Lines
	want(t, decide(pol, []Card{{ID: "c"}}, &l, "bob/qwen", "alice/gemma", "bob/ocr"),
		Action{Start, "c", "qwen", "bob"})
	// the lines remember who came first, whatever order the flows come in
	want(t, decide(pol, []Card{{ID: "c"}}, &l, "alice/gemma", "bob/ocr", "bob/qwen", "carol/pixai"),
		Action{Start, "c", "qwen", "bob"})
	if !reflect.DeepEqual(l.Tenants, []string{"bob", "alice", "carol"}) || !reflect.DeepEqual(l.Models["bob"], []string{"qwen", "ocr"}) {
		t.Errorf("lines: %v", l)
	}
	// nothing free: nothing starts
	want(t, decide(pol, []Card{{ID: "c", State: Starting, Model: "qwen", Owner: "bob"}}, &l, "alice/gemma"))
}

// a model keeps its card until its turn is a quantum old; then it drains,
// stops, and the next tenant's model starts
func TestTurn(t *testing.T) {
	var l Lines
	c := up("c", "gemma", "alice", time.Hour)
	want(t, decide(pol, []Card{c}, &l, "alice/gemma", "bob/qwen"))
	c.TurnAt = ago(3 * time.Hour)
	want(t, decide(pol, []Card{c}, &l, "alice/gemma", "bob/qwen"), Action{Kind: Drain, Card: "c", Model: "gemma"})
	// its turn is over: alice is behind bob now
	if !reflect.DeepEqual(l.Tenants, []string{"bob", "alice"}) {
		t.Errorf("line: %v", l.Tenants)
	}
	c.State = Draining
	want(t, decide(pol, []Card{c}, &l, "alice/gemma", "bob/qwen"))
	c.Inflight = 0
	want(t, decide(pol, []Card{c}, &l, "alice/gemma", "bob/qwen"),
		Action{Kind: Stop, Card: "c", Model: "gemma"}, Action{Start, "c", "qwen", "bob"})
}

// with nobody else to serve, a model keeps its card whatever its age
func TestAloneKeepsTheCard(t *testing.T) {
	var l Lines
	want(t, decide(pol, []Card{up("c", "gemma", "alice", 10*time.Hour)}, &l, "alice/gemma"))
	// in flight with nothing queued is still busy
	want(t, decide(pol, []Card{up("c", "gemma", "alice", time.Hour)}, &l, "bob/qwen"))
}

// [Pass]: the next tenant wants the model that is there: no swap, and the
// turn is new
func TestPass(t *testing.T) {
	var l Lines
	c := up("c", "gemma", "alice", 3*time.Hour)
	want(t, decide(pol, []Card{c}, &l, "alice/gemma", "bob/gemma", "carol/qwen"),
		Action{Pass, "c", "gemma", "bob"})
	// then it is carol's: bob has had his
	c.Owner = "bob"
	want(t, decide(pol, []Card{c}, &l, "alice/gemma", "bob/gemma", "carol/qwen"),
		Action{Kind: Drain, Card: "c", Model: "gemma"})
}

// a tenant's own models take turns too: its turn is up, another of its
// models is on no card, so it moves -- even with nobody else there
func TestOwnModelsTakeTurns(t *testing.T) {
	var l Lines
	want(t, decide(pol, []Card{up("c", "gemma", "alice", 3*time.Hour)}, &l, "alice/gemma", "alice/qwen"),
		Action{Kind: Drain, Card: "c", Model: "gemma"})
	want(t, decide(pol, []Card{{ID: "c"}}, &l, "alice/gemma", "alice/qwen"), Action{Start, "c", "qwen", "alice"})
}

// [GiveWay]: nothing to do and a model is on no card: it goes now,
// whatever its age. [IdleStop]: nothing to do for Idle: it goes.
func TestIdle(t *testing.T) {
	var l Lines
	idle := Card{ID: "c", State: Up, Model: "gemma", Owner: "alice", TurnAt: ago(time.Minute), BusyAt: ago(time.Minute)}
	want(t, decide(pol, []Card{idle}, &l, "bob/qwen"),
		Action{Kind: Stop, Card: "c", Model: "gemma"}, Action{Start, "c", "qwen", "bob"})
	p := Policy{MaxTimeslice: 2 * time.Hour, Idle: 10 * time.Minute}
	want(t, decide(p, []Card{idle}, &l))
	idle.BusyAt = ago(11 * time.Minute)
	want(t, decide(p, []Card{idle}, &l), Action{Kind: Stop, Card: "c", Model: "gemma"})
	want(t, decide(pol, []Card{idle}, &l)) // Idle 0: never
	idle.Inflight = 1
	want(t, decide(p, []Card{idle}, &l))
}

// a turn lasts LoadRatio times the load, when that is longer
func TestLoadRatio(t *testing.T) {
	var l Lines
	p := Policy{MaxTimeslice: 10 * time.Minute, LoadRatio: 4}
	c := up("c", "qwen", "alice", 15*time.Minute)
	c.Load = 5 * time.Minute
	want(t, decide(p, []Card{c}, &l, "alice/qwen", "bob/gemma"))
	c.TurnAt = ago(20 * time.Minute)
	want(t, decide(p, []Card{c}, &l, "alice/qwen", "bob/gemma"), Action{Kind: Drain, Card: "c", Model: "qwen"})
}

// several cards: a model short of cards gets a free one, an owner with
// more cards than the claimant gives one up, and equal holdings are left
// alone
func TestCards(t *testing.T) {
	var l Lines
	old := 3 * time.Hour
	// a copy on a free card
	want(t, decide(pol, []Card{up("c0", "gemma", "alice", old), {ID: "c1"}}, &l, "alice/gemma"),
		Action{Start, "c1", "gemma", "alice"})
	// bob has no card, alice two: bob's model takes one (the older turn)
	l = Lines{}
	cards := []Card{up("c0", "gemma", "alice", old), up("c1", "gemma", "alice", old+time.Minute)}
	want(t, decide(pol, cards, &l, "alice/gemma", "bob/qwen"), Action{Kind: Drain, Card: "c1", Model: "gemma"})
	// one each: nobody takes anything, though both are short of cards
	l = Lines{}
	cards = []Card{up("c0", "gemma", "alice", old), up("c1", "qwen", "bob", old)}
	want(t, decide(pol, cards, &l, "alice/gemma", "bob/qwen"))
	// three and one: a copy takes a card (two and two); two and one: it doesn't
	l = Lines{}
	cards = []Card{up("c0", "gemma", "alice", old), up("c1", "gemma", "alice", old), up("c2", "gemma", "alice", old), up("c3", "qwen", "bob", old)}
	want(t, decide(pol, cards, &l, "alice/gemma", "bob/qwen"), Action{Kind: Drain, Card: "c0", Model: "gemma"})
	l = Lines{}
	want(t, decide(pol, cards[1:], &l, "alice/gemma", "bob/qwen"))
	// an idle card doesn't stop for a copy, only for a model on no card
	l = Lines{}
	idle := Card{ID: "c1", State: Up, Model: "ocr", Owner: "bob", TurnAt: ago(old), BusyAt: ago(time.Minute)}
	want(t, decide(pol, []Card{up("c0", "gemma", "alice", old), idle}, &l, "alice/gemma"))
	want(t, decide(pol, []Card{up("c0", "gemma", "alice", old), idle}, &l, "alice/gemma", "alice/qwen"),
		Action{Kind: Stop, Card: "c1", Model: "ocr"}, Action{Start, "c1", "qwen", "alice"})
}

// Decide is pure: neither the caller's cards nor its lines change
func TestPure(t *testing.T) {
	l := Lines{Tenants: []string{"alice", "bob"}, Models: map[string][]string{"alice": {"gemma"}, "bob": {"qwen"}}}
	cards := []Card{up("c", "gemma", "alice", 3*time.Hour)}
	fs := []Flow{{"alice", "gemma", 5, 1}, {"bob", "qwen", 5, 2}}
	acts, l2 := Decide(cards, fs, map[string]int{"gemma": 4, "qwen": 4}, l, t0, pol)
	if len(acts) != 1 || cards[0].State != Up || l.Tenants[0] != "alice" || l2.Tenants[0] != "bob" {
		t.Errorf("acts %v, cards %v, lines %v -> %v", acts, cards, l, l2)
	}
}

// ---- a simulated machine ---------------------------------------------------

// sim runs Decide against a world, a minute at a time, and checks on every
// decision what spec/Turns.tla claims of every state: no card that is
// answering is stopped (NoKill), no turn is taken before its quantum, a
// round settles (Settles), no card is free while a model wants one and
// none idle while a model is on no card (NoWaste).
type sim struct {
	t      *testing.T
	pol    Policy
	L, D   int // minutes a load and a drain take at most
	rng    *rand.Rand
	cards  []Card
	left   []int     // minutes left loading or draining
	took   []int     // minutes each card's load takes
	dump   io.Writer // if set, every round goes here (cases_test.go)
	q      map[[2]string]int
	oldest map[[2]string]int64
	seq    int64
	slots  map[string]int
	lines  Lines
	minute int
	wait   map[[2]string]int // minutes a flow has had requests queued with its model not up
	upMin  map[string]int    // card-minutes each model was up
	swaps  int
}

func newSim(t *testing.T, cards int, p Policy, L, D int, seed int64) *sim {
	s := &sim{t: t, pol: p, L: L, D: D, rng: rand.New(rand.NewSource(seed)), q: map[[2]string]int{},
		oldest: map[[2]string]int64{}, slots: map[string]int{}, wait: map[[2]string]int{}, upMin: map[string]int{}}
	for i := 0; i < cards; i++ {
		s.cards = append(s.cards, Card{ID: fmt.Sprint("c", i)})
	}
	s.left = make([]int, cards)
	s.took = make([]int, cards)
	return s
}

func (s *sim) now() time.Time { return t0.Add(time.Duration(s.minute) * time.Minute) }

func (s *sim) add(tenant, model string, n int) {
	k := [2]string{tenant, model}
	if s.q[k] == 0 {
		s.seq++
		s.oldest[k] = s.seq
	}
	s.q[k] += n
	s.slots[model] = 2
}

func (s *sim) isUp(model string) bool {
	for _, c := range s.cards {
		if c.State == Up && c.Model == model {
			return true
		}
	}
	return false
}

func (s *sim) flows() []Flow {
	var fs []Flow
	for k, n := range s.q {
		if n > 0 {
			fs = append(fs, Flow{k[0], k[1], n, s.oldest[k]})
		}
	}
	sort.Slice(fs, func(i, j int) bool { return fs[i].Oldest > fs[j].Oldest }) // any order will do
	return fs
}

// step is one minute: loads and drains that are due end, the scheduler
// decides, requests are taken and answered (random: as many as the world
// likes; steady: every slot, every minute), and the clocks move.
func (s *sim) step(steady bool) {
	t, now := s.t, s.now()
	for i := range s.cards {
		c := &s.cards[i]
		if c.State == Starting && s.left[i] == 0 {
			c.State, c.TurnAt, c.BusyAt, c.Load = Up, now, now, time.Duration(s.took[i])*time.Minute
			for k := range s.wait {
				if k[1] == c.Model {
					s.wait[k] = 0
				}
			}
		}
		if c.State == Draining && s.left[i] == 0 {
			c.Inflight = 0
		}
	}
	work := func(m string) int {
		n := 0
		for k, v := range s.q {
			if k[1] == m {
				n += v
			}
		}
		return n
	}
	for i := range s.cards {
		if c := &s.cards[i]; c.State == Starting || c.Inflight > 0 || c.Model != "" && work(c.Model) > 0 {
			c.BusyAt = now
		}
	}
	flows, before := s.flows(), s.lines
	acts, lines := Decide(s.cards, flows, s.slots, s.lines, now, s.pol)
	if s.dump != nil {
		s.writeCase(flows, before, acts, lines)
	}
	s.lines = lines
	if len(acts) > 3*len(s.cards) {
		t.Fatalf("minute %d: a round of %d decisions: %v", s.minute, len(acts), acts)
	}
	for _, a := range acts {
		var i int
		for j := range s.cards {
			if s.cards[j].ID == a.Card {
				i = j
			}
		}
		c := &s.cards[i]
		age := now.Sub(c.TurnAt)
		switch a.Kind {
		case Start:
			if c.State != Down {
				t.Fatalf("minute %d: %v on a card that is %v", s.minute, a, c.State)
			}
			*c = Card{ID: c.ID, State: Starting, Model: a.Model, Owner: a.Tenant, BusyAt: now}
			s.left[i] = 1 + s.rng.Intn(s.L)
			if steady {
				s.left[i] = s.L
			}
			s.took[i] = s.left[i]
			s.swaps++
		case Stop:
			if c.Inflight > 0 {
				t.Fatalf("minute %d: %v stops a card with %d in flight", s.minute, a, c.Inflight)
			}
			*c = Card{ID: c.ID}
		case Drain:
			if c.State != Up || age < s.pol.MaxTimeslice {
				t.Fatalf("minute %d: %v on a card that is %v, its turn %s old", s.minute, a, c.State, age)
			}
			c.State = Draining
			s.left[i] = s.rng.Intn(s.D + 1)
			if steady {
				s.left[i] = s.D
			}
		case Pass:
			if c.State != Up || age < s.pol.MaxTimeslice || a.Model != c.Model {
				t.Fatalf("minute %d: %v on a card that is %v with %s, its turn %s old", s.minute, a, c.State, c.Model, age)
			}
			c.Owner, c.TurnAt = a.Tenant, now
		}
	}
	if again, _ := Decide(s.cards, s.flows(), s.slots, s.lines, now, s.pol); len(again) > 0 {
		// (a drain that ended at once: [Drained] is next)
		for _, a := range again {
			if a.Kind == Drain || a.Kind == Pass {
				t.Fatalf("minute %d: the round had not settled: %v then %v", s.minute, acts, again)
			}
		}
	}
	// NoWaste
	lost, free, idle := "", false, false
	for k, n := range s.q {
		placed := false
		for _, c := range s.cards {
			placed = placed || (c.State == Starting || c.State == Up) && c.Model == k[1]
		}
		if n > 0 && !placed {
			lost = k[1]
		}
	}
	for _, c := range s.cards {
		free = free || c.State == Down
		idle = idle || c.State == Up && c.Inflight == 0 && work(c.Model) == 0
	}
	if lost != "" && (free || idle) {
		t.Fatalf("minute %d: %s is on no card, and a card is free (%v) or idle (%v): %v", s.minute, lost, free, idle, s.cards)
	}
	// the world: requests are taken and answered
	for i := range s.cards {
		c := &s.cards[i]
		if c.State != Up {
			continue
		}
		s.upMin[c.Model]++
		if steady || s.rng.Intn(2) == 0 {
			c.Inflight = 0
		}
		var ks [][2]string
		for k, n := range s.q {
			if k[1] == c.Model && n > 0 {
				ks = append(ks, k)
			}
		}
		sort.Slice(ks, func(i, j int) bool { return ks[i][0] < ks[j][0] })
		for len(ks) > 0 && c.Inflight < s.slots[c.Model] && (steady || s.rng.Intn(3) > 0) {
			j := s.rng.Intn(len(ks))
			s.q[ks[j]]--
			c.Inflight++
			if s.q[ks[j]] == 0 {
				s.wait[ks[j]] = 0
				ks = append(ks[:j], ks[j+1:]...)
			}
		}
	}
	// a minute passes
	for i, c := range s.cards {
		if s.left[i] > 0 && (c.State == Starting || c.State == Draining) {
			s.left[i]--
		}
	}
	for k, n := range s.q {
		if n > 0 && !s.isUp(k[1]) {
			s.wait[k]++
		}
	}
	s.minute++
}

// The spec's claim (Bounded), against Decide itself: worlds that do their
// worst -- requests arriving and being taken at random, loads and drains
// taking up to their limits -- on one card or several. A flow with queued
// requests has its model up within min(T*k, T*(M - 1)) turns, its own
// drain and its own load: T tenants, M models, k of them its own tenant's;
// a turn is a load, a timeslice and a drain. And everything sim checks on
// the way.
func TestNoStarvation(t *testing.T) {
	for seed := int64(0); seed < 200; seed++ {
		rng := rand.New(rand.NewSource(seed))
		T, M, G := 1+rng.Intn(4), 1+rng.Intn(5), 1+rng.Intn(3)
		Q, L, D := 1+rng.Intn(20), 1+rng.Intn(4), 1+rng.Intn(4)
		s := newSim(t, G, Policy{MaxTimeslice: time.Duration(Q) * time.Minute, Idle: time.Duration(rng.Intn(3)) * time.Minute}, L, D, seed)
		k, bound := make([]int, T), map[string]int{} // how many models each tenant uses: ti's are mi, mi+1, ...
		for ti := range k {
			k[ti] = 1 + rng.Intn(M)
			bound[fmt.Sprint("t", ti)] = min(T*k[ti], T*(M-1))*(L+Q+D) + D + L
		}
		busy := 2 + rng.Intn(8) // how often requests arrive
		for s.minute < 2000 {
			for ti := 0; ti < T; ti++ {
				for j := 0; j < k[ti]; j++ {
					if rng.Intn(busy) == 0 {
						s.add(fmt.Sprint("t", ti), fmt.Sprint("m", (ti+j)%M), 1+rng.Intn(6))
					}
				}
			}
			s.step(false)
			for f, w := range s.wait {
				if w > bound[f[0]] {
					t.Fatalf("seed %d (T=%d M=%d G=%d Q=%d L=%d D=%d, models per tenant %v), minute %d: %v waited %d minutes, bound %d",
						seed, T, M, G, Q, L, D, k, s.minute, f, w, bound[f[0]])
				}
			}
		}
	}
}

// saturate keeps every flow full and runs for a while; it returns each
// model's share of the card-minutes that anything was up
func saturate(s *sim, minutes int, flows ...[2]string) map[string]float64 {
	for s.minute < minutes {
		for _, f := range flows {
			if s.q[f] < 100 {
				s.add(f[0], f[1], 100)
			}
		}
		s.step(true)
	}
	total := 0
	for _, n := range s.upMin {
		total += n
	}
	share := map[string]float64{}
	for m, n := range s.upMin {
		share[m] = float64(n) / float64(total)
	}
	return share
}

func near(a, b float64) bool { return a-b < 0.03 && b-a < 0.03 }

// Turns belong to tenants, not models. Alice and Bob share one model and
// Carol has another: two thirds of the time for the shared one, a third
// each -- and its two turns run back to back, without a swap between.
func TestTenantsShareEvenly(t *testing.T) {
	s := newSim(t, 1, Policy{MaxTimeslice: 30 * time.Minute}, 2, 1, 1)
	share := saturate(s, 20000, [2]string{"alice", "gemma"}, [2]string{"bob", "gemma"}, [2]string{"carol", "qwen"})
	if !near(share["gemma"], 2.0/3) {
		t.Errorf("shares %v, want gemma 2/3", share)
	}
	// a cycle is two swaps and three turns: 2 loads + 3 timeslices + 2 drains
	if cycles := 20000 / (2*2 + 3*30 + 2*1); s.swaps > 2*cycles+2 {
		t.Errorf("%d swaps in %d cycles", s.swaps, cycles)
	}
}

// A tenant can't get more by spreading over models: Alice has four, Bob
// one, and Bob's still has half the time.
func TestSpreadingBuysNothing(t *testing.T) {
	s := newSim(t, 1, Policy{MaxTimeslice: 30 * time.Minute}, 2, 1, 1)
	share := saturate(s, 40000, [2]string{"alice", "a"}, [2]string{"alice", "b"}, [2]string{"alice", "c"},
		[2]string{"alice", "d"}, [2]string{"bob", "qwen"})
	if !near(share["qwen"], 0.5) || !near(share["a"], 0.125) || !near(share["d"], 0.125) {
		t.Errorf("shares %v, want qwen 1/2 and alice's 1/8 each", share)
	}
}

// One tenant, one model: nothing ever swaps. Two tenants on one model: the
// same.
func TestNoSwapWithoutNeed(t *testing.T) {
	s := newSim(t, 1, Policy{MaxTimeslice: 5 * time.Minute}, 2, 1, 1)
	saturate(s, 5000, [2]string{"alice", "gemma"}, [2]string{"bob", "gemma"})
	if s.swaps != 1 {
		t.Errorf("%d loads, want 1", s.swaps)
	}
}

// Cards are shared by tenant too. Four cards, two tenants with one model
// each and more work than cards: two cards each, and once there, nothing
// swaps. Three cards: two and one, and it stays (a copy doesn't take a
// card it would have to give back).
func TestCardsShareEvenly(t *testing.T) {
	for _, n := range []int{4, 3} {
		s := newSim(t, n, Policy{MaxTimeslice: 10 * time.Minute}, 2, 1, 1)
		saturate(s, 200, [2]string{"alice", "gemma"})
		before := s.swaps
		if before != n {
			t.Errorf("%d cards: alice alone loaded %d copies", n, before)
		}
		s.upMin = map[string]int{}
		share := saturate(s, 10200, [2]string{"alice", "gemma"}, [2]string{"bob", "qwen"})
		wantShare := map[int]float64{4: 0.5, 3: 1.0 / 3}[n]
		if !near(share["qwen"], wantShare) {
			t.Errorf("%d cards: shares %v, want qwen %.2f", n, share, wantShare)
		}
		if moved := s.swaps - before; moved != n/2 {
			t.Errorf("%d cards: %d loads after bob came, want %d", n, moved, n/2)
		}
	}
}

// A timeslice of zero must not make a round endless: two tenants on one
// model would pass the turn between them for ever (found while proving in
// Lean that a round ends). A turn that began this instant can't be taken.
func TestZeroTimeslice(t *testing.T) {
	done := make(chan []Action, 1)
	go func() {
		var l Lines
		done <- decide(Policy{}, []Card{up("c", "gemma", "alice", time.Hour)}, &l, "alice/gemma", "bob/gemma")
	}()
	select {
	case acts := <-done:
		want(t, acts, Action{Pass, "c", "gemma", "bob"})
	case <-time.After(5 * time.Second):
		t.Fatal("Decide does not return")
	}
}
