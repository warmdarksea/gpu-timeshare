package sched

import (
	"fmt"
	"math/rand"
	"reflect"
	"testing"
	"time"
)

var t0 = time.Date(2026, 11, 8, 12, 0, 0, 0, time.UTC)

var pol = Policy{MaxTimeslice: 2 * time.Hour, Capacity: 1.0}

func decide(slice time.Time, ms ...Model) []Action { return Decide(ms, slice, t0, pol) }

func want(t *testing.T, got []Action, w ...Action) {
	t.Helper()
	if len(w) == 0 {
		w = nil
	}
	if !reflect.DeepEqual(got, w) {
		t.Errorf("got %v, want %v", got, w)
	}
}

// never loaded, all of them: the smallest goes first
func TestSmallestFirst(t *testing.T) {
	want(t, decide(time.Time{},
		Model{Name: "qwen", Cost: 0.95, Ready: 10},
		Model{Name: "pixai", Cost: 0.15, Ready: 3},
		Model{Name: "deepseek-ocr", Cost: 0.32, Ready: 5}),
		Action{Start, "pixai"})
}

func TestOneStartAtATime(t *testing.T) {
	want(t, decide(time.Time{},
		Model{Name: "pixai", Cost: 0.15, State: Starting},
		Model{Name: "deepseek-ocr", Cost: 0.32, Ready: 5}))
}

// the turn's model doesn't fit, but the next one joins the slice
func TestJoinsTheSlice(t *testing.T) {
	want(t, decide(t0,
		Model{Name: "deepseek-ocr", Cost: 0.32, State: Up, Ready: 4},
		Model{Name: "qwen", Cost: 0.95, Ready: 9},
		Model{Name: "joycaption", Cost: 0.6, Ready: 2, LedAt: t0.Add(-time.Hour)}),
		Action{Start, "joycaption"})
}

func TestIdleMakesRoom(t *testing.T) {
	want(t, decide(t0,
		Model{Name: "deepseek-ocr", Cost: 0.32, State: Up},
		Model{Name: "joycaption", Cost: 0.6, State: Up},
		Model{Name: "qwen", Cost: 0.95, Ready: 9}),
		Action{Stop, "joycaption"}, Action{Stop, "deepseek-ocr"})
}

// largest first, and only as many as it takes
func TestIdleMakesJustEnoughRoom(t *testing.T) {
	want(t, decide(t0,
		Model{Name: "pixai", Cost: 0.15, State: Up},
		Model{Name: "joycaption", Cost: 0.6, State: Up},
		Model{Name: "llamaguard", Cost: 0.9, Ready: 1}),
		Action{Stop, "joycaption"}, Action{Stop, "pixai"})
	want(t, decide(t0,
		Model{Name: "pixai", Cost: 0.15, State: Up},
		Model{Name: "joycaption", Cost: 0.6, State: Up},
		Model{Name: "deepseek-ocr", Cost: 0.32, Ready: 1}),
		Action{Stop, "joycaption"})
}

func TestTheSliceKeepsTheCardUntilItsTime(t *testing.T) {
	gemma := Model{Name: "gemma", Cost: 0.95, State: Up, Ready: 50, Inflight: 8, LedAt: t0.Add(-3 * time.Hour)}
	qwen := Model{Name: "qwen", Cost: 0.95, Ready: 3}
	want(t, decide(t0.Add(-time.Hour), gemma, qwen))
	want(t, decide(t0.Add(-3*time.Hour), gemma, qwen), Action{Drain, "gemma"})
	// draining, with requests in flight: wait; once they're done: stop
	gemma.State = Draining
	want(t, decide(t0.Add(-3*time.Hour), gemma, qwen))
	gemma.Inflight = 0
	want(t, decide(t0.Add(-3*time.Hour), gemma, qwen), Action{Stop, "gemma"}, Action{Start, "qwen"})
}

func TestNobodyWaitingNobodyGivesWay(t *testing.T) {
	want(t, decide(t0.Add(-10*time.Hour),
		Model{Name: "gemma", Cost: 0.95, State: Up, Ready: 50, Inflight: 8},
		Model{Name: "qwen", Cost: 0.95}))
}

// Two medium models hold the card and a big one waits: the slice goes
// together. The old rotation drained one model at a time, and only one
// whose leaving alone made room, so it waited for ever.
func TestTheSliceGoesTogether(t *testing.T) {
	want(t, decide(t0.Add(-3*time.Hour),
		Model{Name: "a", Cost: 0.5, State: Up, Ready: 9},
		Model{Name: "b", Cost: 0.5, State: Up, Ready: 9},
		Model{Name: "qwen", Cost: 0.95, Ready: 1}),
		Action{Drain, "a"}, Action{Drain, "b"})
}

// After its time, nothing joins: else a stream of joining models could
// keep a load going and the slice from ever ending (TLC found that one).
func TestNothingJoinsAnExpiredSlice(t *testing.T) {
	ms := []Model{
		{Name: "a", Cost: 0.6, State: Up, Ready: 9},
		{Name: "qwen", Cost: 0.95, Ready: 1},
		{Name: "pixai", Cost: 0.15, Ready: 1, LedAt: t0},
	}
	want(t, Decide(ms, t0.Add(-time.Hour), t0, pol), Action{Start, "pixai"})
	want(t, Decide(ms, t0.Add(-3*time.Hour), t0, pol), Action{Drain, "a"})
}

func TestADrainingSliceTakesNothingNew(t *testing.T) {
	want(t, decide(t0.Add(-3*time.Hour),
		Model{Name: "a", Cost: 0.5, State: Draining, Inflight: 1},
		Model{Name: "pixai", Cost: 0.15, Ready: 1}))
}

func TestIdleModelStops(t *testing.T) {
	p := Policy{MaxTimeslice: 2 * time.Hour, Idle: 10 * time.Minute, Capacity: 1.0}
	quiet := Model{Name: "qwen", Cost: 0.95, State: Up, BusyAt: t0.Add(-11 * time.Minute)}
	want(t, Decide([]Model{quiet}, t0, t0, p), Action{Stop, "qwen"})
	recent := quiet
	recent.BusyAt = t0.Add(-9 * time.Minute)
	want(t, Decide([]Model{recent}, t0, t0, p))
	working := quiet
	working.Inflight = 1
	want(t, Decide([]Model{working}, t0, t0, p))
	ready := quiet
	ready.Ready = 3
	want(t, Decide([]Model{ready}, t0, t0, p))
	want(t, Decide([]Model{quiet}, t0, t0, pol)) // Idle 0: never
	// its room counts as free in the same round: the waiting model starts
	want(t, Decide([]Model{{Name: "gemma", Cost: 0.9, Ready: 2}, quiet}, t0, t0, p),
		Action{Stop, "qwen"}, Action{Start, "gemma"})
	// Decide is pure: the caller's models are untouched
	ms := []Model{quiet}
	Decide(ms, t0, t0, p)
	if ms[0].State != Up {
		t.Error("Decide changed its argument")
	}
}

// The spec's claim, against Decide itself: a world that does its worst --
// work arriving and running out at random, loads and drains taking up to
// their limits -- and a model with work spends at most n slices' time off
// the card (a slice: MaxLoad + MaxTimeslice + MaxLoad + MaxDrain) before
// it leads one, unless its work runs out first. Joining a slice pauses the
// count without resetting it, as in the spec. Time is in minutes; the
// rules run until they settle between minutes, as the driver's rounds do.
func TestNoStarvation(t *testing.T) {
	costs := []float64{0.15, 0.32, 0.5, 0.6, 0.9, 0.95, 1.0}
	for seed := int64(0); seed < 500; seed++ {
		rng := rand.New(rand.NewSource(seed))
		n := 2 + rng.Intn(4)
		T, L, D := 1+rng.Intn(30), 1+rng.Intn(5), 1+rng.Intn(5)
		p := Policy{MaxTimeslice: time.Duration(T) * time.Minute, Capacity: 1.0,
			Idle: time.Duration(rng.Intn(3)) * time.Minute}
		bound := n * (L + T + L + D)

		type sim struct {
			Model
			left, wait int // minutes left loading or draining; minutes off the card with work
		}
		ms := make([]*sim, n)
		for i := range ms {
			ms[i] = &sim{Model: Model{Name: fmt.Sprint("m", i), Cost: costs[rng.Intn(len(costs))]}}
		}
		var slice time.Time
		onCard := func() bool {
			for _, m := range ms {
				if m.State != Down {
					return true
				}
			}
			return false
		}
		for minute := 0; minute < 3000; minute++ {
			now := t0.Add(time.Duration(minute) * time.Minute)
			// the world
			for _, m := range ms {
				switch {
				case rng.Intn(4) == 0:
					m.Ready++
				case m.State == Up && m.Ready > 0 && rng.Intn(3) == 0:
					if m.Ready--; m.Ready == 0 {
						m.wait = 0 // its work ran out
					}
				}
				if m.State == Starting && m.left == 0 {
					m.State = Up
					if slice.IsZero() { // the lead: as the driver does
						slice, m.LedAt, m.wait = now, now, 0
					}
				}
				if m.State == Draining && m.left == 0 {
					m.Inflight = 0
				}
			}
			// the driver: rounds until nothing changes
			for round := 0; ; round++ {
				if round > 10 {
					t.Fatalf("seed %d: the rules don't settle", seed)
				}
				if !onCard() {
					slice = time.Time{}
				}
				var in []Model
				for _, m := range ms {
					if m.Ready > 0 || m.Inflight > 0 || m.State == Starting {
						m.BusyAt = now
					}
					in = append(in, m.Model)
				}
				acts := Decide(in, slice, now, p)
				if len(acts) == 0 {
					break
				}
				for _, a := range acts {
					var m *sim
					for _, x := range ms {
						if x.Name == a.Model {
							m = x
						}
					}
					switch a.Kind {
					case Start:
						if !onCard() {
							slice = time.Time{}
						}
						m.State, m.left = Starting, 1+rng.Intn(L)
					case Stop:
						m.State = Down
					case Drain:
						m.State, m.Inflight, m.left = Draining, 1, rng.Intn(D+1)
					}
				}
				used := 0.0
				for _, m := range ms {
					if m.State != Down {
						used += m.Cost
					}
				}
				if used > p.Capacity+eps {
					t.Fatalf("seed %d, minute %d: %.2f on the card", seed, minute, used)
				}
			}
			// a minute passes
			for _, m := range ms {
				if m.left > 0 && (m.State == Starting || m.State == Draining) {
					m.left--
				}
				if m.Ready > 0 && m.State != Up {
					if m.wait++; m.wait > bound {
						t.Fatalf("seed %d (n=%d T=%d L=%d D=%d), minute %d: %s waited %d minutes, bound %d",
							seed, n, T, L, D, minute, m.Name, m.wait, bound)
					}
				}
			}
		}
	}
}

// Expired, with an idle model on the card: the slice ends rather than
// making room. Making room instead lets a model ahead in the turn join,
// run dry, be stopped and come back with work, round after round, without
// ever leading (TLC found that one; the simulation can't, as nothing
// arrives between its rounds).
func TestAnExpiredSliceEndsBeforeMakingRoom(t *testing.T) {
	ms := []Model{
		{Name: "lead", Cost: 0.5, State: Up, Ready: 3, LedAt: t0.Add(-3 * time.Hour)},
		{Name: "joiner", Cost: 0.5, State: Up},
		{Name: "big", Cost: 0.5, Ready: 1},
	}
	want(t, Decide(ms, t0.Add(-time.Hour), t0, pol), Action{Stop, "joiner"})
	want(t, Decide(ms, t0.Add(-3*time.Hour), t0, pol), Action{Drain, "lead"}, Action{Drain, "joiner"})
}
