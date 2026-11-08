package sched

import (
	"sort"
	"time"
)

// What Decide sees and says, and the primitives it reads in. Decide itself
// is in policy.go.

type State int

const (
	Down State = iota
	Starting
	Up
	Draining // finishing what's in flight, taking nothing new, then stops
)

func (s State) String() string { return [...]string{"down", "starting", "up", "draining"}[s] }

// Model is what the policy sees of one model.
type Model struct {
	Name     string
	Cost     float64 // its share of capacity
	State    State
	Inflight int       // requests being answered
	Ready    int       // requests queued for it
	BusyAt   time.Time // the last time it had work (ready or in flight)
	LedAt    time.Time // when it last led a slice: its load, as the slice's first (zero: never)
}

// Policy is Decide's knobs.
type Policy struct {
	MaxTimeslice time.Duration // a slice keeps the card this long while another model waits
	Idle         time.Duration // an up model with no work for this long stops (0: never)
	Capacity     float64       // what the costs of the models on the card must fit in
}

type ActionKind int

const (
	Start ActionKind = iota
	Stop
	Drain
)

func (k ActionKind) String() string { return [...]string{"start", "stop", "drain"}[k] }

type Action struct {
	Kind  ActionKind
	Model string
}

const eps = 1e-9

// Card is every model, on the card or not. Decide works on its own copy:
// a model it stops is Down for the rest of the round.
type Card []Model

func (c Card) onCard(m Model) bool { return m.State != Down }

func (c Card) used() float64 {
	u := 0.0
	for _, m := range c {
		if c.onCard(m) {
			u += m.Cost
		}
	}
	return u
}

// waiting: it has requests and isn't on the card
func waiting(m Model) bool { return m.State == Down && m.Ready > 0 }

// idle: up, with nothing queued or in flight
func idle(m Model) bool { return m.State == Up && m.Ready == 0 && m.Inflight == 0 }

func (c Card) any(f func(Model) bool) bool {
	for _, m := range c {
		if f(m) {
			return true
		}
	}
	return false
}

// inTurn is the waiting models, the one that led a slice longest ago first
// (never counts as longest; ties go to the smallest, then by name).
func (c Card) inTurn() []Model {
	var w []Model
	for _, m := range c {
		if waiting(m) {
			w = append(w, m)
		}
	}
	sort.Slice(w, func(i, j int) bool {
		if !w[i].LedAt.Equal(w[j].LedAt) {
			return w[i].LedAt.Before(w[j].LedAt)
		}
		if w[i].Cost != w[j].Cost {
			return w[i].Cost < w[j].Cost
		}
		return w[i].Name < w[j].Name
	})
	return w
}

// idleLargestFirst: the idle models, the ones freeing most room first.
func (c Card) idleLargestFirst() []Model {
	var out []Model
	for _, m := range c {
		if idle(m) {
			out = append(out, m)
		}
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].Cost != out[j].Cost {
			return out[i].Cost > out[j].Cost
		}
		return out[i].Name < out[j].Name
	})
	return out
}

// leave: m is off the card (its place in the turn stays: see LedAt)
func (c Card) leave(name string) {
	for i := range c {
		if c[i].Name == name {
			c[i].State = Down
		}
	}
}
