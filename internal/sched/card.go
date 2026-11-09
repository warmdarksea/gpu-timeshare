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
	State    State
	Inflight int       // requests being answered
	Ready    int       // requests queued for it
	BusyAt   time.Time // the last time it had work (ready or in flight)
	LoadedAt time.Time // when it last finished loading (zero: never)
}

// Policy is Decide's knobs.
type Policy struct {
	MaxTimeslice time.Duration // a model keeps the card this long after loading while another waits
	Idle         time.Duration // an up model with no work for this long stops (0: never)
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

// Card is every model, on the card or not. Decide works on its own copy:
// a model it stops is Down for the rest of the round.
type Card []Model

func onCard(m Model) bool { return m.State != Down }

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

// inTurn is the waiting models, the one that loaded longest ago first
// (never counts as longest; ties go by name).
func (c Card) inTurn() []Model {
	var w []Model
	for _, m := range c {
		if waiting(m) {
			w = append(w, m)
		}
	}
	sort.Slice(w, func(i, j int) bool {
		if !w[i].LoadedAt.Equal(w[j].LoadedAt) {
			return w[i].LoadedAt.Before(w[j].LoadedAt)
		}
		return w[i].Name < w[j].Name
	})
	return w
}
