//go:build !leansched

package sched

import "time"

// decideRound is the scheduler the driver runs: here, Decide.
// (With -tags leansched it is the Lean model, lean.go.)
func decideRound(cards []Card, flows []Flow, slots map[string]int, lines Lines, now time.Time, pol Policy) ([]Action, Lines) {
	return Decide(cards, flows, slots, lines, now, pol)
}

// Engine names the scheduler in use, for the log.
const Engine = "go"
