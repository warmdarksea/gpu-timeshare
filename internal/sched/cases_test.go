package sched

import (
	"bufio"
	"fmt"
	"math/rand"
	"os"
	"strings"
	"testing"
	"time"
)

// The Lean model of Decide (proof/Timeshare/Policy.lean) is checked against
// Decide itself: TestCases writes every round of a few hundred simulated
// worlds -- Decide's arguments and its answer -- to $TIMESHARE_CASES, and
// proof/Check.lean runs the model on each and compares. `nix-build -A
// tests.lean` does both. The format is in Check.lean.

func minutes(t time.Time) int {
	if t.IsZero() {
		return 0
	}
	return int(t.Sub(t0) / time.Minute)
}

func dash(s string) string {
	if s == "" {
		return "-"
	}
	return s
}

func writeLines(w *strings.Builder, word string, l Lines) {
	for _, t := range l.Tenants {
		fmt.Fprintf(w, "%s %s %s\n", word, t, strings.Join(l.Models[t], " "))
	}
}

func (s *sim) writeCase(flows []Flow, before Lines, acts []Action, after Lines) {
	var w strings.Builder
	fmt.Fprintf(&w, "case %d %d %d %d\n", s.minute, s.pol.MaxTimeslice/time.Minute, int(s.pol.LoadRatio), s.pol.Idle/time.Minute)
	for _, c := range s.cards {
		fmt.Fprintf(&w, "card %s %s %s %s %s %d %d %d %d\n", c.ID, c.State, dash(c.Model), dash(c.Owner), dash(c.Next),
			c.Inflight, minutes(c.TurnAt), minutes(c.BusyAt), c.Load/time.Minute)
	}
	for _, f := range flows {
		fmt.Fprintf(&w, "flow %s %s %d %d\n", f.Tenant, f.Model, f.Queued, f.Oldest)
	}
	for m, n := range s.slots {
		fmt.Fprintf(&w, "slot %s %d\n", m, n)
	}
	writeLines(&w, "line", before)
	for _, a := range acts {
		fmt.Fprintf(&w, "act %s %s %s %s %s\n", a.Kind, a.Card, dash(a.Model), dash(a.Tenant), dash(a.For))

	}
	writeLines(&w, "out", after)
	w.WriteString("end\n")
	s.dump.Write([]byte(w.String()))
}

func TestCases(t *testing.T) {
	path := os.Getenv("TIMESHARE_CASES")
	if path == "" {
		path = t.TempDir() + "/cases"
	}
	f, err := os.Create(path)
	if err != nil {
		t.Fatal(err)
	}
	out := bufio.NewWriter(f)
	for seed := int64(0); seed < 300; seed++ {
		rng := rand.New(rand.NewSource(1000 + seed))
		T, M, G := 1+rng.Intn(4), 1+rng.Intn(5), 1+rng.Intn(4)
		p := Policy{MaxTimeslice: time.Duration(1+rng.Intn(12)) * time.Minute, LoadRatio: float64(rng.Intn(4)),
			Idle: time.Duration(rng.Intn(4)) * time.Minute}
		s := newSim(t, G, p, 1+rng.Intn(4), 1+rng.Intn(3), seed)
		s.dump = out
		busy := 2 + rng.Intn(10)
		for s.minute < 300 {
			for ti := 0; ti < T; ti++ {
				for mi := 0; mi < M; mi++ {
					if rng.Intn(busy) == 0 {
						s.add(fmt.Sprint("t", ti), fmt.Sprint("m", mi), 1+rng.Intn(8))
					}
				}
			}
			s.step(false)
		}
	}
	if err := out.Flush(); err != nil {
		t.Fatal(err)
	}
	f.Close()
}
