package sched

import (
	"fmt"
	"math/rand"
	"os"
	"reflect"
	"strconv"
	"strings"
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

// Names are whatever they are: spaces, a dash, nothing at all (the one
// card of a machine with no gpus setting has no name).
func TestLeanNames(t *testing.T) {
	now := time.Unix(1_700_000_000, 0)
	pol := Policy{MaxTimeslice: time.Minute, LoadRatio: 1.5}
	cards := []Card{
		{ID: "", State: Up, Model: "big model", Owner: "al ice", Inflight: 1, TurnAt: now.Add(-time.Hour), BusyAt: now, Load: 7 * time.Second},
		{ID: "card two"},
	}
	flows := []Flow{{"al ice", "big model", 3, 5}, {"-", "big model", 1, 6}, {"-", "ünï cödé", 2, 7}, {"bob\tb", "-", 4, 8}}
	slots := map[string]int{"big model": 2, "ünï cödé": 1, "-": 3}
	lines := Lines{Tenants: []string{"al ice"}, Models: map[string][]string{"al ice": {"big model"}}}
	for round := 0; round < 4; round++ {
		goActs, goLines := Decide(cards, flows, slots, lines, now, pol)
		leanActs, leanLines := DecideLean(cards, flows, slots, lines, now, pol)
		if len(goActs) == 0 && round == 0 {
			t.Fatal("the round decides nothing: it tests nothing")
		}
		if !reflect.DeepEqual(goActs, leanActs) || !reflect.DeepEqual(goLines.Tenants, leanLines.Tenants) ||
			!reflect.DeepEqual(goLines.Models, leanLines.Models) {
			t.Fatalf("round %d:\n go:   %+v %v\n lean: %+v %v", round, goActs, goLines, leanActs, leanLines)
		}
		lines = goLines
		now = now.Add(2 * time.Minute)
	}
}

func rssKB(t *testing.T) int {
	b, err := os.ReadFile("/proc/self/status")
	if err != nil {
		t.Skip(err)
	}
	for _, line := range strings.Split(string(b), "\n") {
		if strings.HasPrefix(line, "VmRSS:") {
			n, _ := strconv.Atoi(strings.Fields(line)[1])
			return n
		}
	}
	t.Skip("no VmRSS")
	return 0
}

// ffi/schedule.c counts Lean's references by hand, and a miscount is
// silent: one too few and every call leaks its arguments or its answer,
// one too many and Lean frees what is still in use. Many calls, then: the
// process must not grow (a leak of one small object a call would be tens
// of megabytes here), and must not crash.
func TestLeanKeepsCount(t *testing.T) {
	now := time.Unix(1_700_000_000, 0)
	pol := Policy{MaxTimeslice: time.Minute, LoadRatio: 1.5}
	cards := []Card{
		{ID: "0", State: Up, Model: "a", Owner: "alice", Inflight: 1, TurnAt: now.Add(-time.Hour), BusyAt: now, Load: 7 * time.Second},
		{ID: "1"}, {ID: "2", State: Draining, Model: "b", Owner: "bob", Next: "c", Inflight: 2},
	}
	flows := []Flow{{"alice", "a", 3, 5}, {"bob", "c", 1, 6}, {"carol", "d", 2, 7}, {"carol", "a", 4, 8}}
	slots := map[string]int{"a": 2, "b": 1, "c": 3, "d": 1}
	lines := Lines{Tenants: []string{"alice", "bob"}, Models: map[string][]string{"alice": {"a"}, "bob": {"c"}}}
	by := map[string][]caseReq{"alice": {{"r1", "k1"}, {"r2", "k2"}}, "bob": {{"r3", "k1"}, {"r4", "k3"}}, "carol": {{"r5", "k4"}}}
	inflight := map[string]int{"alice": 1}
	call := func(n int) {
		for i := 0; i < n; i++ {
			if acts, _ := DecideLean(cards, flows, slots, lines, now, pol); len(acts) == 0 {
				t.Fatal("nothing decided")
			}
			if picked, last := RoundRobinLean(by, func(r caseReq) string { return r.key }, inflight, Owner{"bob", 0, 4}, "alice", 3); len(picked) != 3 || last == "" {
				t.Fatalf("picked %v, last %q", picked, last)
			}
		}
	}
	call(20000) // whatever the allocators keep for themselves, they have by now
	before := rssKB(t)
	call(100000)
	grown := rssKB(t) - before
	t.Logf("%d kB more after 100,000 rounds", grown)
	if grown > 8*1024 {
		t.Fatalf("the process grew by %d kB over 100,000 rounds: something is not released", grown)
	}
}
