// Package sched decides which models are on the card and feeds them
// requests. Decide (this file) is the whole scheduling algorithm; card.go
// has its types and primitives, driver.go applies its decisions.
package sched

import "time"

// Decide is one round of the scheduling algorithm. spec/Timeslice.tla is
// its model, rule for rule ([Name] is the action there). TLC checks there,
// for every way models can pack onto the card, that a model with work
// leads a slice within n slices' time (n models; a slice lasts at most a
// load, MaxTimeslice, a load and a drain), or its work runs out.
//
// The models on the card form one *slice*. Its *lead* is the model it
// started with, and its clock (slice: zero until the lead has loaded, and
// with no slice; the driver keeps it, and stamps the lead's LedAt) starts
// at that load. Waiting models take turns: the one that led longest ago
// goes first. A waiting model that fits beside the slice joins it, without
// extending it and without spending its turn. Once the slice has run
// MaxTimeslice while any model waits, nothing joins any more, and the
// whole slice drains.
func Decide(models []Model, slice, now time.Time, pol Policy) []Action {
	c := append(Card(nil), models...)
	var out []Action
	stop := func(m Model) { out = append(out, Action{Stop, m.Name}); c.leave(m.Name) }
	fits := func(m Model) bool { return c.used()+m.Cost <= pol.Capacity+eps }

	// [Drained] a draining model with nothing in flight leaves. [IdleStop]
	// so does one with no work for pol.Idle: an empty queue empties the card.
	for _, m := range c {
		if m.State == Draining && m.Inflight == 0 ||
			idle(m) && pol.Idle > 0 && now.Sub(m.BusyAt) >= pol.Idle {
			stop(m)
		}
	}
	if !c.any(c.onCard) {
		slice = time.Time{} // an empty card ends the slice
	}
	// One load at a time (vllm sizes its cache from the memory it sees free
	// while loading); a slice that is draining takes nothing new.
	loading := c.any(func(m Model) bool { return m.State == Starting })
	closing := c.any(func(m Model) bool { return m.State == Draining })
	turn := c.inTurn()
	if loading || closing || len(turn) == 0 {
		return out
	}
	first := turn[0]
	withoutIdle := c.used()
	for _, m := range c.idleLargestFirst() {
		withoutIdle -= m.Cost
	}

	switch {
	case !slice.IsZero() && now.Sub(slice) >= pol.MaxTimeslice: // [EndSlice] it has had its time, and a model waits
		for _, m := range c {
			if m.State == Up {
				out = append(out, Action{Drain, m.Name})
			}
		}
	case fits(first): // [Start] its turn, and it fits (on an empty card: it leads)
		out = append(out, Action{Start, first.Name})
	case withoutIdle+first.Cost <= pol.Capacity+eps: // [MakeRoom] idle models stop, largest first
		for _, m := range c.idleLargestFirst() {
			if fits(first) {
				break
			}
			stop(m)
		}
	default: // [Start] it doesn't fit yet: the first after it that does joins the slice
		for _, m := range turn[1:] {
			if fits(m) {
				out = append(out, Action{Start, m.Name})
				break
			}
		}
	}
	return out
}
