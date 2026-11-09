// Package sched decides which model has the card and feeds it requests.
// Decide (this file) is the whole scheduling algorithm; card.go has its
// types and primitives, driver.go applies its decisions.
package sched

import "time"

// Decide is one round of the scheduling algorithm. spec/Timeslice.tla is
// its model, rule for rule ([Name] is the action there). TLC checks there
// that a model with work is served again within (n-1) turns, its own drain
// and its own load (n models; a turn lasts at most a load, MaxTimeslice and
// a drain), or its work runs out.
//
// One model has the card at a time: two busy models on one card each run
// at half speed (measured), so sharing it saves only the swap. The model
// on the card keeps it while it has work, for MaxTimeslice after it loaded
// if another model waits. Waiting models take turns: the one that loaded
// longest ago goes first.
func Decide(models []Model, now time.Time, pol Policy) []Action {
	c := append(Card(nil), models...)
	turn := c.inTurn()
	var out []Action
	for i, m := range c {
		switch {
		case m.State == Draining && m.Inflight == 0: // [Drained] it has finished
		case idle(m) && len(turn) > 0: // [GiveWay] nothing to do, and a model waits
		case idle(m) && pol.Idle > 0 && now.Sub(m.BusyAt) >= pol.Idle: // [IdleStop] the card can power down
		case m.State == Up && len(turn) > 0 && now.Sub(m.LoadedAt) >= pol.MaxTimeslice: // [Expire] its time is up
			out = append(out, Action{Drain, m.Name})
			continue
		default:
			continue
		}
		out = append(out, Action{Stop, m.Name})
		c[i].State = Down
	}
	if len(turn) > 0 && !c.any(onCard) { // [Start] the card is free: whoever's turn it is
		out = append(out, Action{Start, turn[0].Name})
	}
	return out
}
