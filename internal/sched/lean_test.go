package sched

import (
	"fmt"
	"math/rand"
	"reflect"
	"testing"
	"time"
)

// The Lean model, linked in, decides every round of the simulated worlds
// as Decide does: action for action, line for line. This is the check on
// lean.go, which is the part of the Lean scheduler no theorem is about.
func TestLeanAgrees(t *testing.T) {
	rounds := 0
	for seed := int64(0); seed < 60; seed++ {
		rng := rand.New(rand.NewSource(2000 + seed))
		T, M, G := 1+rng.Intn(4), 1+rng.Intn(5), 1+rng.Intn(4)
		p := Policy{MaxTimeslice: time.Duration(1+rng.Intn(12)) * time.Minute, LoadRatio: float64(rng.Intn(7)) / 2,
			Idle: time.Duration(rng.Intn(4)) * time.Minute}
		s := newSim(t, G, p, 1+rng.Intn(4), 1+rng.Intn(3), seed)
		busy := 2 + rng.Intn(10)
		for s.minute < 200 {
			for ti := 0; ti < T; ti++ {
				for mi := 0; mi < M; mi++ {
					if rng.Intn(busy) == 0 {
						s.add(fmt.Sprint("t", ti), fmt.Sprint("m", mi), 1+rng.Intn(8))
					}
				}
			}
			flows := s.flows()
			goActs, goLines := Decide(s.cards, flows, s.slots, s.lines, s.now(), s.pol)
			leanActs, leanLines := DecideLean(s.cards, flows, s.slots, s.lines, s.now(), s.pol)
			if len(goLines.Models) == 0 {
				goLines.Models = map[string][]string{}
			}
			if !reflect.DeepEqual(goActs, leanActs) || !reflect.DeepEqual(goLines.Tenants, leanLines.Tenants) ||
				!reflect.DeepEqual(goLines.Models, leanLines.Models) {
				t.Fatalf("seed %d, minute %d:\n go:   %v %v\n lean: %v %v", seed, s.minute, goActs, goLines, leanActs, leanLines)
			}
			rounds++
			s.step(false)
		}
	}
	t.Logf("%d rounds", rounds)
}

// And it gives a model's free slots to the requests RoundRobin does: names
// with spaces in them, a tenant served last that has nothing queued now, an
// owner with nothing queued.
func TestLeanRoundRobinAgrees(t *testing.T) {
	rng := rand.New(rand.NewSource(11))
	all := []string{"alice", "bob b", "carol", "dave:d", "erin", "-", "zed"}
	for call := 0; call < 5000; call++ {
		names := all[:1+rng.Intn(len(all))]
		by, inflight := map[string][]caseReq{}, map[string]int{}
		id := 0
		for _, n := range names {
			for k := rng.Intn(5); k > 0; k-- {
				id++
				by[n] = append(by[n], caseReq{fmt.Sprint("r", id), fmt.Sprint("k :", rng.Intn(8))})
			}
			inflight[n] = rng.Intn(4)
		}
		pick := func() string {
			if rng.Intn(3) == 0 {
				return ""
			}
			return all[rng.Intn(len(all))]
		}
		own := Owner{Tenant: pick(), Held: rng.Intn(3), Slots: 1 + rng.Intn(6)}
		after, n := pick(), rng.Intn(7)
		key := func(r caseReq) string { return r.key }
		goPicked, goLast := RoundRobin(by, key, inflight, own, after, n)
		leanPicked, leanLast := RoundRobinLean(by, key, inflight, own, after, n)
		if !reflect.DeepEqual(goPicked, leanPicked) || goLast != leanLast {
			t.Fatalf("call %d (after %q, n %d, own %+v, %v, in flight %v):\n go:   %v, last %q\n lean: %v, last %q",
				call, after, n, own, by, inflight, goPicked, goLast, leanPicked, leanLast)
		}
	}
}
