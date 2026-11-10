package sched

// The scheduler, from the Lean model. proof/Timeshare/Policy.lean is the
// algorithm the theorems of proof/Timeshare/Proofs are about. Lean compiles
// it to C; libschedule.a is that, with a C face on it (ffi/schedule.h:
// structs in, structs out), and this file links it and calls it. So the
// functions the proofs are about are the ones that run: DecideLean and
// RoundRobinLean are what the driver calls, and Decide and RoundRobin
// (policy.go) are the same algorithm in Go, to read beside the English and
// for the tests to compare with.
//
// What is not proved is the way there and back: this file (Go's values
// into schedule.h's structs), ffi/schedule.c (those into Lean's values) and
// proof/Timeshare/Export.lean (Lean's values into the model's own types).
// TestLeanAgrees and TestLeanRoundRobinAgrees check all three against
// policy.go.
//
// The Lean runtime wants its calls on a thread it knows, so one goroutine,
// locked to its thread, makes them all.

/*
#include <stdlib.h>
#include <schedule.h>
*/
import "C"

import (
	"runtime"
	"sort"
	"sync"
	"time"
	"unsafe"
)

// Engine names the scheduler in use, for the log.
const Engine = "lean"

var (
	leanOnce  sync.Once
	leanCalls chan func()
)

// onLean runs f on the thread the Lean runtime was started on.
func onLean(f func()) {
	leanOnce.Do(func() {
		leanCalls = make(chan func())
		ready := make(chan bool)
		go func() {
			runtime.LockOSThread()
			ready <- C.ts_init() == 0
			for f := range leanCalls {
				f()
			}
		}()
		if !<-ready {
			panic("the Lean scheduler did not initialize")
		}
	})
	done := make(chan struct{})
	leanCalls <- func() { f(); close(done) }
	<-done
}

// cmem is the C memory one call's arguments live in: C must not be handed
// memory of Go's that holds pointers.
type cmem struct{ ptrs []unsafe.Pointer }

func (m *cmem) free() {
	for _, p := range m.ptrs {
		C.free(p)
	}
}

func (m *cmem) str(s string) *C.char {
	p := C.CString(s)
	m.ptrs = append(m.ptrs, unsafe.Pointer(p))
	return p
}

// opt is str, with "" as schedule.h's "none".
func (m *cmem) opt(s string) *C.char {
	if s == "" {
		return nil
	}
	return m.str(s)
}

// array is n zeroed elements of the given size (nil for none).
func (m *cmem) array(n int, size uintptr) unsafe.Pointer {
	if n == 0 {
		return nil
	}
	p := C.calloc(C.size_t(n), C.size_t(size))
	m.ptrs = append(m.ptrs, p)
	return p
}

func (m *cmem) strs(ss []string) **C.char {
	p := (**C.char)(m.array(len(ss), unsafe.Sizeof((*C.char)(nil))))
	out := unsafe.Slice(p, len(ss))
	for i, s := range ss {
		out[i] = m.str(s)
	}
	return p

}

// u64 is a count or a time for the model, which has no negative numbers.
func u64[N int | int64 | time.Duration](n N) C.uint64_t {
	if n < 0 {
		return 0
	}
	return C.uint64_t(n)
}

func nanos(t time.Time) C.uint64_t {
	if t.IsZero() {
		return 0
	}
	return u64(t.UnixNano())
}

func goStrs(p **C.char, n C.size_t) []string {
	var out []string
	for _, s := range unsafe.Slice(p, int(n)) {
		out = append(out, C.GoString(s))
	}
	return out
}

// DecideLean is Decide, by the Lean model.
func DecideLean(cards []Card, flows []Flow, slots map[string]int, lines Lines, now time.Time, pol Policy) ([]Action, Lines) {
	var m cmem
	defer m.free()

	// the model's load_ratio is a whole number: each card's load comes
	// multiplied already, as Decide's quantum has it
	round := C.ts_round{
		n_cards: C.size_t(len(cards)), n_flows: C.size_t(len(flows)),
		n_slots: C.size_t(len(slots)), n_lines: C.size_t(len(lines.Tenants)),
		now:    nanos(now),
		policy: C.ts_policy{max_timeslice: u64(pol.MaxTimeslice), load_ratio: 1, idle: u64(pol.Idle)},
	}
	round.cards = (*C.ts_card)(m.array(len(cards), C.sizeof_ts_card))
	for i, c := range cards {
		unsafe.Slice(round.cards, len(cards))[i] = C.ts_card{
			id: m.str(c.ID), state: C.ts_state(c.State), model: m.opt(c.Model), owner: m.opt(c.Owner), next: m.opt(c.Next),
			inflight: u64(c.Inflight), turn_at: nanos(c.TurnAt), busy_at: nanos(c.BusyAt),
			load: u64(time.Duration(pol.LoadRatio * float64(c.Load))),
		}
	}
	round.flows = (*C.ts_flow)(m.array(len(flows), C.sizeof_ts_flow))
	for i, f := range flows {
		unsafe.Slice(round.flows, len(flows))[i] = C.ts_flow{
			tenant: m.str(f.Tenant), model: m.str(f.Model), queued: u64(f.Queued), oldest: u64(f.Oldest),
		}
	}
	round.slots = (*C.ts_slots)(m.array(len(slots), C.sizeof_ts_slots))
	i := 0
	for name, n := range slots {
		unsafe.Slice(round.slots, len(slots))[i] = C.ts_slots{model: m.str(name), slots: u64(n)}
		i++
	}
	round.lines = (*C.ts_line)(m.array(len(lines.Tenants), C.sizeof_ts_line))
	for i, t := range lines.Tenants {
		ms := lines.Models[t]
		unsafe.Slice(round.lines, len(lines.Tenants))[i] = C.ts_line{
			tenant: m.str(t), models: m.strs(ms), n_models: C.size_t(len(ms)),
		}
	}

	var d *C.ts_decision
	onLean(func() { d = C.ts_decide(&round) })
	if d == nil {
		panic("the Lean scheduler could not decide the round")
	}
	defer C.ts_decision_free(d)

	var acts []Action
	for _, a := range unsafe.Slice(d.actions, int(d.n_actions)) {
		// (C.GoString of NULL, schedule.h's "none", is "")
		acts = append(acts, Action{Kind: ActionKind(a.kind), Card: C.GoString(a.card), Model: C.GoString(a.model),
			Tenant: C.GoString(a.tenant), For: C.GoString(a.next)})
	}
	out := Lines{Models: map[string][]string{}}
	for _, l := range unsafe.Slice(d.lines, int(d.n_lines)) {
		t := C.GoString(l.tenant)
		out.Tenants = append(out.Tenants, t)
		if l.n_models > 0 {
			out.Models[t] = goStrs(l.models, l.n_models)
		}
	}
	return acts, out
}

// RoundRobinLean is RoundRobin, by the Lean model.
func RoundRobinLean[R any](byTenant map[string][]R, key func(R) string, inflight map[string]int, own Owner, after string, n int) ([]R, string) {
	var tenants []string
	for t, rs := range byTenant {
		if len(rs) > 0 {
			tenants = append(tenants, t)
		}
	}
	if len(tenants) == 0 || n <= 0 {
		return nil, ""
	}
	sort.Strings(tenants) // schedule.h: the queues in the order of their tenants' names

	var m cmem
	defer m.free()
	queues := (*C.ts_queue)(m.array(len(tenants), C.sizeof_ts_queue))
	for i, t := range tenants {
		keys := make([]string, len(byTenant[t]))
		for j, r := range byTenant[t] {
			keys[j] = key(r)
		}
		unsafe.Slice(queues, len(tenants))[i] = C.ts_queue{
			tenant: m.str(t), inflight: u64(inflight[t]), keys: m.strs(keys), n_keys: C.size_t(len(keys)),
		}
	}
	owner := C.ts_owner{tenant: m.opt(own.Tenant), held: u64(own.Held), slots: u64(own.Slots)}
	last := m.opt(after)

	var p *C.ts_picks
	onLean(func() { p = C.ts_round_robin(queues, C.size_t(len(tenants)), owner, last, u64(n)) })
	if p == nil {
		panic("the Lean scheduler could not pick the requests")
	}
	defer C.ts_picks_free(p)

	var picked []R
	for _, k := range unsafe.Slice(p.picks, int(p.n_picks)) {
		picked = append(picked, byTenant[tenants[k.queue]][k.request])
	}
	if len(picked) == 0 {
		return nil, ""
	}
	return picked, C.GoString(p.last)
}
