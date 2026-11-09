package sched

import (
	"fmt"
	"math/rand"
	"reflect"
	"testing"
	"time"
)

var t0 = time.Date(2026, 11, 8, 12, 0, 0, 0, time.UTC)

var pol = Policy{MaxTimeslice: 2 * time.Hour}

func decide(ms ...Model) []Action { return Decide(ms, t0, pol) }

func want(t *testing.T, got []Action, w ...Action) {
	t.Helper()
	if len(w) == 0 {
		w = nil
	}
	if !reflect.DeepEqual(got, w) {
		t.Errorf("got %v, want %v", got, w)
	}
}

func ago(d time.Duration) time.Time { return t0.Add(-d) }

// the one that loaded longest ago goes first; never loaded is longest ago
func TestTurns(t *testing.T) {
	want(t, decide(
		Model{Name: "qwen", Ready: 10},
		Model{Name: "deepseek-ocr", Ready: 5}),
		Action{Start, "deepseek-ocr"})
	want(t, decide(
		Model{Name: "deepseek-ocr", Ready: 5, LoadedAt: ago(time.Hour)},
		Model{Name: "qwen", Ready: 10, LoadedAt: ago(3 * time.Hour)}),
		Action{Start, "qwen"})
	want(t, decide(
		Model{Name: "deepseek-ocr", Ready: 5, LoadedAt: ago(time.Hour)},
		Model{Name: "qwen", Ready: 10}),
		Action{Start, "qwen"})
}

func TestOneAtATime(t *testing.T) {
	want(t, decide(
		Model{Name: "pixai", State: Starting},
		Model{Name: "deepseek-ocr", Ready: 5}))
}

func TestKeepsTheCardUntilItsTime(t *testing.T) {
	gemma := Model{Name: "gemma", State: Up, Ready: 50, Inflight: 8, LoadedAt: ago(time.Hour)}
	qwen := Model{Name: "qwen", Ready: 3}
	want(t, decide(gemma, qwen))
	gemma.LoadedAt = ago(3 * time.Hour)
	want(t, decide(gemma, qwen), Action{Drain, "gemma"})
	// draining, with requests in flight: wait; once they're done: stop, and the next starts
	gemma.State = Draining
	want(t, decide(gemma, qwen))
	gemma.Inflight = 0
	want(t, decide(gemma, qwen), Action{Stop, "gemma"}, Action{Start, "qwen"})
}

// in flight with nothing queued is still busy: it keeps its time
func TestInFlightIsBusy(t *testing.T) {
	want(t, decide(
		Model{Name: "gemma", State: Up, Inflight: 1, LoadedAt: ago(time.Hour)},
		Model{Name: "qwen", Ready: 3}))
}

func TestNobodyWaitingNobodyGivesWay(t *testing.T) {
	want(t, decide(
		Model{Name: "gemma", State: Up, Ready: 50, Inflight: 8, LoadedAt: ago(10 * time.Hour)},
		Model{Name: "qwen"}))
}

// nothing to do and a model waits: it goes now, whatever its time
func TestGiveWay(t *testing.T) {
	want(t, decide(
		Model{Name: "gemma", State: Up, LoadedAt: ago(time.Minute), BusyAt: t0},
		Model{Name: "qwen", Ready: 3}),
		Action{Stop, "gemma"}, Action{Start, "qwen"})
}

func TestIdleModelStops(t *testing.T) {
	p := Policy{MaxTimeslice: 2 * time.Hour, Idle: 10 * time.Minute}
	quiet := Model{Name: "qwen", State: Up, BusyAt: ago(11 * time.Minute)}
	want(t, Decide([]Model{quiet}, t0, p), Action{Stop, "qwen"})
	recent := quiet
	recent.BusyAt = ago(9 * time.Minute)
	want(t, Decide([]Model{recent}, t0, p))
	working := quiet
	working.Inflight = 1
	want(t, Decide([]Model{working}, t0, p))
	ready := quiet
	ready.Ready = 3
	want(t, Decide([]Model{ready}, t0, p))
	want(t, Decide([]Model{quiet}, t0, pol)) // Idle 0: never
	// Decide is pure: the caller's models are untouched
	ms := []Model{quiet}
	Decide(ms, t0, p)
	if ms[0].State != Up {
		t.Error("Decide changed its argument")
	}
}

// The spec's claim, against Decide itself: a world that does its worst --
// work arriving and running out at random, loads and drains taking up to
// their limits -- and a model with work spends at most (n-1) turns, its own
// drain and its own load not serving (a turn: MaxLoad + MaxTimeslice +
// MaxDrain) before it loads, unless its work runs out first. And never two
// models on the card. Time is in minutes; the rules run until they settle between
// minutes, as the driver's rounds do.
func TestNoStarvation(t *testing.T) {
	for seed := int64(0); seed < 500; seed++ {
		rng := rand.New(rand.NewSource(seed))
		n := 2 + rng.Intn(5)
		T, L, D := 1+rng.Intn(30), 1+rng.Intn(5), 1+rng.Intn(5)
		p := Policy{MaxTimeslice: time.Duration(T) * time.Minute,
			Idle: time.Duration(rng.Intn(3)) * time.Minute}
		bound := (n-1)*(L+T+D) + L + D

		type sim struct {
			Model
			left, wait int // minutes left loading or draining; minutes off the card with work
		}
		ms := make([]*sim, n)
		for i := range ms {
			ms[i] = &sim{Model: Model{Name: fmt.Sprint("m", i)}}
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
					m.State, m.LoadedAt, m.wait = Up, now, 0
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
				var in []Model
				for _, m := range ms {
					if m.Ready > 0 || m.Inflight > 0 || m.State == Starting {
						m.BusyAt = now
					}
					in = append(in, m.Model)
				}
				acts := Decide(in, now, p)
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
						m.State, m.left = Starting, 1+rng.Intn(L)
					case Stop:
						m.State = Down
					case Drain:
						m.State, m.Inflight, m.left = Draining, 1, rng.Intn(D+1)
					}
				}
				on := 0
				for _, m := range ms {
					if m.State != Down {
						on++
					}
				}
				if on > 1 {
					t.Fatalf("seed %d, minute %d: %d models on the card", seed, minute, on)
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
