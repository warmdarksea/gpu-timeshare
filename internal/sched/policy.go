// Package sched decides which models are loaded and feeds them jobs.
//
// The constraint is VRAM, not job count, and loading takes minutes. The
// policy (Decide) is a pure function of the models' states, so it tests
// without processes; the driver (Scheduler) applies its decisions.
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
	Draining // finishing what's in flight, taking nothing new, then stops
)

func (s State) String() string { return [...]string{"down", "starting", "up", "draining"}[s] }

// Model is what the policy sees of one model.
type Model struct {
	Name     string
	Cost     float64 // its share of capacity
	State    State
	UpSince  time.Time
	Inflight int       // requests being answered
	Ready    int       // jobs that could be sent now
	BusyAt   time.Time // the last time it had work (ready or in flight)
	LastOn   time.Time // the last time it was on the card (zero: never)
}

// Policy is Decide's knobs.
type Policy struct {
	Rotation time.Duration // a busy model gives way after this, if others wait
	Idle     time.Duration // an up model with no work for this long stops (0: never)
	Budget   float64       // capacity: what the loaded models' costs must fit in
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

// Decide is one round of the policy:
//
//  1. a draining model with nothing in flight stops, and so does an up
//     model that has had no work for the idle period -- so an empty queue
//     leaves the card with no process on it, free to power down;
//  2. one start at a time (vllm sizes its KV cache from memory measured
//     while starting; a neighbour starting concurrently makes it lie);
//  3. models already up are drained first (by the driver); when models
//     with ready jobs aren't up, they take turns: the one off the card
//     longest goes first (never loaded counts as longest; ties go to the
//     smallest), or the first after it that fits beside what's up;
//  4. if none fits, stop idle models to make room for the first in turn;
//  5. if that isn't enough, rotate: a busy model up longer than the
//     rotation period drains, so a steady stream for one model can't
//     starve the rest. It finishes what's in flight, then stops, and
//     goes to the back of the turn: with three big models waiting, they
//     take the card in order, a rotation period each.
func Decide(models []Model, now time.Time, pol Policy) []Action {
	rotation, budget := pol.Rotation, pol.Budget
	models = append([]Model(nil), models...) // the idle rule marks its stops Down
	var out []Action
	used, starting, draining := 0.0, false, false
	for i, m := range models {
		if m.State == Up && m.Ready == 0 && m.Inflight == 0 && pol.Idle > 0 && now.Sub(m.BusyAt) >= pol.Idle {
			out = append(out, Action{Stop, m.Name})
			models[i].State = Down // gone, for the rest of the round
			continue
		}
		switch m.State {
		case Draining:
			if m.Inflight == 0 {
				out = append(out, Action{Stop, m.Name})
				continue
			}
			draining = true
			used += m.Cost
		case Starting:
			starting = true
			used += m.Cost
		case Up:
			used += m.Cost
		}
	}
	if starting {
		return out
	}
	var wanted []Model
	for _, m := range models {
		if m.State == Down && m.Ready > 0 {
			wanted = append(wanted, m)
		}
	}
	if len(wanted) == 0 {
		return out
	}
	sort.Slice(wanted, func(i, j int) bool {
		if !wanted[i].LastOn.Equal(wanted[j].LastOn) {
			return wanted[i].LastOn.Before(wanted[j].LastOn)
		}
		if wanted[i].Cost != wanted[j].Cost {
			return wanted[i].Cost < wanted[j].Cost
		}
		return wanted[i].Name < wanted[j].Name
	})
	for _, w := range wanted {
		if used+w.Cost <= budget+eps {
			return append(out, Action{Start, w.Name})
		}
	}
	// nothing fits: idle models make room first
	need := wanted[0].Cost - (budget - used)
	var idle []Model
	for _, m := range models {
		if m.State == Up && m.Ready == 0 && m.Inflight == 0 {
			idle = append(idle, m)
		}
	}
	sort.Slice(idle, func(i, j int) bool { return idle[i].Cost > idle[j].Cost })
	freed := 0.0
	var stops []Action
	for _, m := range idle {
		if freed >= need-eps {
			break
		}
		freed += m.Cost
		stops = append(stops, Action{Stop, m.Name})
	}
	if freed >= need-eps {
		return append(out, stops...)
	}
	if draining {
		return out // room is already being made
	}
	// rotation: the longest-up busy model gives way, if that makes room
	var busy []Model
	for _, m := range models {
		if m.State == Up && (m.Ready > 0 || m.Inflight > 0) && now.Sub(m.UpSince) >= rotation {
			busy = append(busy, m)
		}
	}
	sort.Slice(busy, func(i, j int) bool { return busy[i].UpSince.Before(busy[j].UpSince) })
	for _, m := range busy {
		if freed+m.Cost >= need-eps {
			return append(append(out, stops...), Action{Drain, m.Name})
		}
	}
	return out
}
