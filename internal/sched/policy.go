// Package sched decides which model is on which card and feeds it
// requests. This file is the whole scheduling algorithm: Decide (the cards)
// and RoundRobin (the requests of a model that is up). driver.go applies
// what they say. spec/Turns.tla is Decide's model, rule for rule ([Name]
// here is the action there), and doc/VERIFICATION.md describes both and
// what TLC checks. Change the three together.
//
// The words:
//
//   - a flow is one tenant's queued requests for one model;
//   - a card (a GPU) holds one model at a time, and its time is cut into
//     turns. A turn belongs to a tenant, but every tenant with requests
//     for the model that is up gets them answered during it;
//   - tenants with queued requests stand in one line, and each tenant
//     keeps a line of its own models. Whoever is first has waited longest:
//     a tenant goes to the back when a turn of its ends, a model when it
//     leaves a card, and newcomers join at the back;
//   - a model is lost when it has queued requests and is on no card, and
//     short when it is on a card but has more queued than its cards can
//     take.
//
// The rules, in the order Decide tries them, until none applies:
//
//	[Drained]   a draining card with nothing in flight stops. It is kept for
//	            the tenant and the model it drained for.
//	[Start]     a card that drained for somebody loads their model. A free
//	            card goes to the first tenant with a lost model (failing
//	            that, a short one): fewest cards first, then the line. It
//	            loads that tenant's first lost model.
//	[GiveWay]   no card is free and a model is lost: an idle card stops.
//	[IdleStop]  a card idle for Policy.Idle stops.
//	[Pass]      a turn is a quantum old, and the tenant with the best
//	            claim to the card wants the model that is there: the turn
//	            is that tenant's now. Nothing is swapped.
//	[Drain]     as [Pass], but it wants another model: the turn is that
//	            tenant's now, for that model. The card takes no more
//	            requests and finishes the ones in flight; [Drained] and
//	            [Start] follow, and nobody else can have the card
//	            meanwhile. Any number of cards may drain at once.
//
// The best claim to a card whose turn is a quantum old ([Pass], [Drain]):
// a tenant may move a lost model there, stay (it has queued requests for
// the model that is there), or copy a short model there if it would still
// hold fewer cards than the owner afterwards. Among those, fewest cards
// first, then the line; the owner, who has had its turn, counts one card
// fewer and comes last among equals. The winner moves if it can, else
// stays, else copies. If the winner is the owner and stays, nothing
// happens: with nobody else to serve, a model keeps its card for ever.
//
// What that gives (doc/VERIFICATION.md, section 4): no turn ends before
// its quantum unless the card is idle, so swapping costs at most
// (load + drain) per quantum; and a flow whose tenant has queued requests
// for k models, among T tenants with requests and M models with requests,
// sees its model up within min(T*k, T*(M - 1)) turns plus its own
// drain and load, however much the others have queued.
package sched

import (
	"sort"
	"time"
)

type State int

const (
	Down State = iota
	Starting
	Up
	Draining // finishing what's in flight, taking nothing new, then it stops and loads Next
)

func (s State) String() string { return [...]string{"down", "starting", "up", "draining"}[s] }

// Card is one GPU, as the policy sees it.
type Card struct {
	ID       string
	State    State
	Model    string        // what is on it ("" when down)
	Owner    string        // the tenant whose turn it is; of a card that drains or has drained, whose it will be
	Next     string        // what it drains for, or has drained for: the model it loads next ("": nothing)
	Inflight int           // requests being answered on it
	TurnAt   time.Time     // when this turn began: the load finished, or the turn passed
	BusyAt   time.Time     // the last time it had work
	Load     time.Duration // how long the model took to load
}

// Flow is one tenant's queued requests for one model (not the ones in flight).
type Flow struct {
	Tenant, Model string
	Queued        int
	Oldest        int64 // its oldest queued request: newcomers join the lines in this order
}

// Lines is what the scheduler remembers between rounds: who has waited
// longest. Tenants holds the tenants with queued requests, Models each
// tenant's models with queued requests; the first is served first.
type Lines struct {
	Tenants []string
	Models  map[string][]string
}

// Policy is Decide's knobs.
type Policy struct {
	MaxTimeslice time.Duration // a turn can't be taken before it is this old
	LoadRatio    float64       // nor before it is this many times the model's load time
	Idle         time.Duration // an idle card stops after this long (0: never)
}

// quantum is how old a turn on c must be before somebody else can have it.
func (p Policy) quantum(c Card) time.Duration {
	if l := time.Duration(p.LoadRatio * float64(c.Load)); l > p.MaxTimeslice {
		return l
	}
	return p.MaxTimeslice
}

type ActionKind int

const (
	Start ActionKind = iota // load Model on Card; the turn is Tenant's
	Stop                    // stop what is on Card
	Drain                   // send Card no more requests; once it has finished it loads For, for Tenant
	Pass                    // the turn on Card is Tenant's now
)

func (k ActionKind) String() string { return [...]string{"start", "stop", "drain", "pass"}[k] }

type Action struct {
	Kind   ActionKind
	Card   string
	Model  string
	Tenant string
	For    string // Drain: the model the card drains for
}

// Decide is one round of the scheduling algorithm: what to do with the
// cards now, and the lines as they are afterwards. It is pure. slots is
// how many requests each model answers at once on one card.
func Decide(cards []Card, flows []Flow, slots map[string]int, lines Lines, now time.Time, pol Policy) ([]Action, Lines) {
	w := &world{cards: append([]Card(nil), cards...), flows: flows, slots: slots, lines: lines.join(flows), now: now, pol: pol}
	var out []Action
	for {
		a, ok := w.rule()
		if !ok {
			return out, w.lines
		}
		out = append(out, a)
	}
}

// rule applies the first rule that has something to do.
func (w *world) rule() (Action, bool) {
	// [Drained]: it stops, and stays its next tenant's
	for i, c := range w.cards {
		if c.State == Draining && c.Inflight == 0 {
			w.cards[i] = Card{ID: c.ID, Owner: c.Owner, Next: c.Next}
			return Action{Kind: Stop, Card: c.ID, Model: c.Model}, true
		}
	}
	// [Start]: a card that drained for somebody
	for i, c := range w.cards {
		if c.State == Down && c.Next != "" {
			w.cards[i] = Card{ID: c.ID, State: Starting, Model: c.Next, Owner: c.Owner}
			return Action{Kind: Start, Card: c.ID, Model: c.Next, Tenant: c.Owner}, true
		}
	}
	free := w.find(func(c Card) bool { return c.State == Down })
	// [Start]: a free card
	if t, m, ok := w.claim(); ok && free >= 0 {
		w.cards[free] = Card{ID: w.cards[free].ID, State: Starting, Model: m, Owner: t}
		return Action{Kind: Start, Card: w.cards[free].ID, Model: m, Tenant: t}, true
	}
	// [GiveWay]: the card that has been idle longest
	if free < 0 && w.anyLost() {
		if i := w.longestIdle(0); i >= 0 {
			return w.stop(i), true
		}
	}
	// [IdleStop]
	if w.pol.Idle > 0 {
		if i := w.longestIdle(w.pol.Idle); i >= 0 {
			return w.stop(i), true
		}
	}
	// [Pass]
	for i, c := range w.cards {
		if t, m, ok := w.winner(c); ok && t != c.Owner && m == c.Model {
			w.lines.toBack(c.Owner)
			w.cards[i].Owner, w.cards[i].TurnAt = t, w.now
			return Action{Kind: Pass, Card: c.ID, Model: m, Tenant: t}, true
		}
	}
	// [Drain]: from the owner with the most cards, the oldest turn first.
	// (A free card would have been started on instead: [Start] comes first.)
	best := -1
	for i, c := range w.cards {
		if _, m, ok := w.winner(c); !ok || m == c.Model {
			continue
		}
		if b := w.cards[max(best, 0)]; best < 0 || w.held(c.Owner) > w.held(b.Owner) ||
			w.held(c.Owner) == w.held(b.Owner) && c.TurnAt.Before(b.TurnAt) {
			best = i
		}
	}
	if best >= 0 && free < 0 {
		c := w.cards[best]
		t, m, _ := w.winner(c)
		w.lines.Ended(c.Owner, c.Model) // the old turn is over; the new one is the winner's
		w.cards[best].State, w.cards[best].Owner, w.cards[best].Next = Draining, t, m
		return Action{Kind: Drain, Card: c.ID, Model: c.Model, Tenant: t, For: m}, true
	}

	return Action{}, false
}

// winner is the tenant with the best claim to c, whose turn is a quantum
// old, and the model it would have there. (None if the turn is younger.)
func (w *world) winner(c Card) (tenant, model string, ok bool) {
	// (nor if it began this instant: a turn that has just passed can't pass
	// again, so a round ends even with a quantum of zero)
	if age := w.now.Sub(c.TurnAt); c.State != Up || age < w.pol.quantum(c) || age <= 0 {
		return "", "", false
	}
	rank := func(t string) int { // fewest cards first; the owner counts one fewer, and comes last among equals
		if t == c.Owner {
			return 2*(w.held(t)-1) + 1
		}
		return 2 * w.held(t)
	}
	for _, t := range w.lines.Tenants { // in line order: the first of the lowest rank wins
		m, can := w.lost(t) // move
		if !can && w.queued(t, c.Model) > 0 {
			m, can = c.Model, true // stay
		}
		if !can && t != c.Owner && w.held(t)+2 <= w.held(c.Owner) {
			m, can = w.short(t, c.Model) // copy
		}
		if can && (!ok || rank(t) < rank(tenant)) {
			tenant, model, ok = t, m, true
		}
	}
	return tenant, model, ok
}

// claim is who gets a free card, and for which model: the first tenant
// with a lost model or a short one (fewest cards first, then the line),
// and its first lost model, else its first short one.
func (w *world) claim() (tenant, model string, ok bool) {
	for _, t := range w.lines.Tenants {
		m, can := w.lost(t)
		if !can {
			m, can = w.short(t, "")
		}
		if can && (!ok || w.held(t) < w.held(tenant)) {
			tenant, model, ok = t, m, true
		}
	}
	return tenant, model, ok
}

// stop ends the turn on an idle card.
func (w *world) stop(i int) Action {
	c := w.cards[i]
	w.cards[i] = Card{ID: c.ID}
	w.lines.Ended(c.Owner, c.Model)
	return Action{Kind: Stop, Card: c.ID, Model: c.Model}
}

// ---- the lines -------------------------------------------------------------

// Ended is the end of a turn: its tenant goes to the back of the line,
// and its model to the back of every tenant's (they all had it). Decide
// does this for the turns it ends; the driver for the ones that end by
// themselves (a load that fails, a server that dies).
func (l *Lines) Ended(tenant, model string) {
	l.toBack(tenant)
	for t := range l.Models {
		l.Models[t] = toBack(l.Models[t], model)
	}
}

func (l *Lines) toBack(tenant string) { l.Tenants = toBack(l.Tenants, tenant) }

// toBack moves x to the end of s, if it is there.
func toBack(s []string, x string) []string {
	for i, y := range s {
		if y == x {
			return append(append(s[:i:i], s[i+1:]...), x)
		}
	}
	return s
}

// join is the lines for these flows (a copy): whoever has nothing queued
// any more leaves, and newcomers join at the back, the one with the oldest
// request first.
func (l Lines) join(flows []Flow) Lines {
	flows = append([]Flow(nil), flows...)
	sort.SliceStable(flows, func(i, j int) bool { return flows[i].Oldest < flows[j].Oldest })
	queued := map[[2]string]bool{}
	for _, f := range flows {
		if f.Queued > 0 {
			queued[[2]string{f.Tenant, f.Model}] = true
			queued[[2]string{f.Tenant}] = true
		}
	}
	out := Lines{Models: map[string][]string{}}
	seen := map[[2]string]bool{}
	add := func(t, m string) {
		if k := [2]string{t}; queued[k] && !seen[k] {
			seen[k] = true
			out.Tenants = append(out.Tenants, t)
		}
		if k := [2]string{t, m}; m != "" && queued[k] && !seen[k] {
			seen[k] = true
			out.Models[t] = append(out.Models[t], m)
		}
	}
	for _, t := range l.Tenants {
		add(t, "")
		for _, m := range l.Models[t] {
			add(t, m)
		}
	}
	for _, f := range flows {
		add(f.Tenant, f.Model)
	}
	return out
}

// ---- what the rules ask about the world --------------------------------------

// world is Decide's copy of the cards and the lines: a rule that applies
// changes it, and the next rule sees the change.
type world struct {
	cards []Card
	flows []Flow
	slots map[string]int
	lines Lines
	now   time.Time
	pol   Policy
}

func serving(c Card) bool { return c.State == Starting || c.State == Up }

func (w *world) find(f func(Card) bool) int {
	for i, c := range w.cards {
		if f(c) {
			return i
		}
	}
	return -1
}

// queued is how many requests tenant t has queued for model m ("": anybody).
func (w *world) queued(t, m string) int {
	n := 0
	for _, f := range w.flows {
		if f.Model == m && (t == "" || f.Tenant == t) {
			n += f.Queued
		}
	}
	return n
}

// held is how many cards have a turn of t's: its model is loading or up
// there, or the card drains (or has drained) for it.
func (w *world) held(t string) int {
	n := 0
	for _, c := range w.cards {
		if (serving(c) || c.Next != "") && c.Owner == t { // (a card that is serving has no Next)
			n++
		}
	}
	return n
}

// room is how many more requests m's cards can take, and whether it is on
// a card at all -- or will be: a card that drains for m counts as m's.
func (w *world) room(m string) (n int, placed bool) {
	for _, c := range w.cards {
		switch {
		case serving(c):
			if c.Model == m {
				n, placed = n+w.slots[m]-c.Inflight, true
			}
		case c.Next == m && m != "":
			n, placed = n+w.slots[m], true

		}
	}
	return n, placed
}

// lost is t's first model that has queued requests and is on no card.
func (w *world) lost(t string) (string, bool) {
	for _, m := range w.lines.Models[t] {
		if _, placed := w.room(m); !placed {
			return m, true
		}
	}
	return "", false
}

func (w *world) anyLost() bool {
	for _, t := range w.lines.Tenants {
		if _, ok := w.lost(t); ok {
			return true
		}
	}
	return false
}

// short is t's first model, other than except, that is on a card and has
// more queued than its cards can take.
func (w *world) short(t, except string) (string, bool) {
	for _, m := range w.lines.Models[t] {
		if r, placed := w.room(m); m != except && placed && w.queued("", m) > r {
			return m, true
		}
	}
	return "", false
}

// longestIdle is the card that is up with nothing queued or in flight
// for at least d, and for longest (-1: none).
func (w *world) longestIdle(d time.Duration) int {
	best := -1
	for i, c := range w.cards {
		if c.State == Up && c.Inflight == 0 && w.queued("", c.Model) == 0 && w.now.Sub(c.BusyAt) >= d &&
			(best < 0 || c.BusyAt.Before(w.cards[best].BusyAt)) {
			best = i
		}
	}
	return best
}

// ---- the requests of a model that is up --------------------------------------

// Owner is the tenant whose turn it is on a card, for RoundRobin: how many
// of the card's Slots its requests hold now.
type Owner struct {
	Tenant      string
	Held, Slots int
}

// RoundRobin picks up to n of a model's queued requests for its free
// slots. Each goes to the tenant with the fewest requests in flight (so
// the slots are shared evenly, however long each tenant's requests run),
// and among those to the next after the tenant served last; a tenant's own
// requests go in the order given. No two picks have the same key (the
// same question is asked once). It returns the picks and the tenant
// served last. So a tenant with a queued request for a model that is up
// waits for at most one request of each other tenant.
//
// One exception, for the tenant whose turn it is on the card (own): while
// it holds fewer than half the card's slots and has a request to give, the
// free slot is its. Everybody with requests for the model is answered
// during a turn, and at once -- but the turn's owner keeps half of it,
// whoever else rides. (Without this a tenant could take its own turns on
// one model and half of everybody else's on another.)
func RoundRobin[R any](byTenant map[string][]R, key func(R) string, inflight map[string]int, own Owner, after string, n int) ([]R, string) {
	var tenants []string
	for t, rs := range byTenant {
		if len(rs) > 0 {
			tenants = append(tenants, t)
		}
	}
	sort.Strings(tenants)
	var picked []R
	keys, next, got := map[string]bool{}, map[string]int{}, map[string]int{}
	for len(picked) < n {
		// the tenants that still have a request nobody picked, starting after the one served last
		start := sort.SearchStrings(tenants, after)
		if start < len(tenants) && tenants[start] == after {
			start++
		}
		best := ""
		for i := range tenants {
			t := tenants[(start+i)%len(tenants)]
			for next[t] < len(byTenant[t]) && keys[key(byTenant[t][next[t]])] {
				next[t]++
			}
			if next[t] < len(byTenant[t]) && (best == "" || inflight[t]+got[t] < inflight[best]+got[best]) {
				best = t
			}
		}
		if best == "" {
			break
		}
		if o := own.Tenant; o != "" && next[o] < len(byTenant[o]) && own.Held+got[o] < (own.Slots+1)/2 {
			best = o // the owner's half
		}
		r := byTenant[best][next[best]]
		keys[key(r)] = true
		picked = append(picked, r)
		got[best]++
		after = best
	}
	if len(picked) == 0 {
		return nil, ""
	}
	return picked, after
}
