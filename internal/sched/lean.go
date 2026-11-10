//go:build leansched

package sched

// The scheduler, from the Lean model. proof/Timeshare/Policy.lean is the
// algorithm the theorems of proof/Timeshare/Proofs are about; lake compiles
// it to C and into libScheduler.a, and this file links that and calls it.
// With -tags leansched, the function the proofs are about is the one that
// runs: Decide (policy.go) is then only what the tests compare it with.
//
// What is not proved is this file: turning Decide's arguments into the text
// the model reads (proof/Timeshare/Text.lean) and its answer back.
// TestLeanAgrees checks that against Decide on every round of the simulated
// worlds.
//
// The Lean runtime wants its calls on a thread it knows, so one goroutine,
// locked to its thread, makes them all.

/*
#include <stdlib.h>
#include <string.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module();
extern void lean_io_mark_end_initialization();
extern lean_object* initialize_timeshare_x2dmodel_Timeshare_Text(uint8_t builtin);
extern lean_object* timeshare_decide(lean_object*);

static int ts_init(void) {
	lean_initialize_runtime_module();
	lean_object* r = initialize_timeshare_x2dmodel_Timeshare_Text(1);
	int ok = lean_io_result_is_ok(r);
	lean_dec_ref(r);
	if (ok) lean_io_mark_end_initialization();
	return ok ? 0 : 1;
}

static char* ts_decide(const char* in) {
	lean_object* r = timeshare_decide(lean_mk_string(in));
	char* out = strdup(lean_string_cstr(r));
	lean_dec(r);
	return out;
}
*/
import "C"

import (
	"fmt"
	"runtime"
	"strings"
	"sync"
	"time"
	"unsafe"
)

// Engine names the scheduler in use, for the log.
const Engine = "lean"

type leanCall struct {
	in  string
	out chan string
}

var (
	leanOnce  sync.Once
	leanCalls chan leanCall
)

// leanDecide hands one round, as text, to the model.
func leanDecide(in string) string {
	leanOnce.Do(func() {
		leanCalls = make(chan leanCall)
		ready := make(chan error)
		go func() {
			runtime.LockOSThread()
			if C.ts_init() != 0 {
				ready <- fmt.Errorf("the Lean scheduler did not initialize")
				return
			}
			ready <- nil
			for c := range leanCalls {
				cin := C.CString(c.in)
				cout := C.ts_decide(cin)
				C.free(unsafe.Pointer(cin))
				c.out <- C.GoString(cout)
				C.free(unsafe.Pointer(cout))
			}
		}()
		if err := <-ready; err != nil {
			panic(err)
		}
	})
	c := leanCall{in: in, out: make(chan string, 1)}
	leanCalls <- c
	return <-c.out
}

// plain: the name can go into a line of words as it is.
func plain(s string) bool {
	return s != "" && s != "-" && !strings.ContainsAny(s, " \t\r\n")
}

func nanos(t time.Time) int64 {
	if t.IsZero() {
		return 0
	}
	return t.UnixNano()
}

// DecideLean is Decide, by the Lean model. A name the text can't carry (a
// space in it) is the one thing it leaves to Decide.
func DecideLean(cards []Card, flows []Flow, slots map[string]int, lines Lines, now time.Time, pol Policy) ([]Action, Lines) {
	ok := true
	word := func(s string) string {
		if s == "" {
			return "-"
		}
		ok = ok && plain(s)
		return s
	}
	var b strings.Builder
	// the model's load_ratio is a whole number: each card's load comes
	// multiplied already, as Decide's quantum has it
	fmt.Fprintf(&b, "case %d %d 1 %d\n", nanos(now), int64(pol.MaxTimeslice), int64(pol.Idle))
	for _, c := range cards {
		fmt.Fprintf(&b, "card %s %s %s %s %s %d %d %d %d\n", word(c.ID), c.State, word(c.Model), word(c.Owner),
			word(c.Next), c.Inflight, nanos(c.TurnAt), nanos(c.BusyAt), int64(time.Duration(pol.LoadRatio*float64(c.Load))))
	}
	for _, f := range flows {
		fmt.Fprintf(&b, "flow %s %s %d %d\n", word(f.Tenant), word(f.Model), f.Queued, f.Oldest)
	}
	for m, n := range slots {
		fmt.Fprintf(&b, "slot %s %d\n", word(m), n)
	}
	for _, t := range lines.Tenants {
		fmt.Fprintf(&b, "line %s", word(t))
		for _, m := range lines.Models[t] {
			b.WriteString(" " + word(m))
		}
		b.WriteString("\n")
	}
	if !ok {
		return Decide(cards, flows, slots, lines, now, pol)
	}
	unword := func(s string) string {
		if s == "-" {
			return ""
		}
		return s
	}
	var acts []Action
	out := Lines{Models: map[string][]string{}}
	for _, line := range strings.Split(leanDecide(b.String()), "\n") {
		w := strings.Fields(line)
		switch {
		case len(w) == 0:
		case w[0] == "act" && len(w) == 6:
			kind, known := map[string]ActionKind{"start": Start, "stop": Stop, "drain": Drain, "pass": Pass}[w[1]]
			if !known {
				panic("the Lean scheduler answered " + line)
			}
			acts = append(acts, Action{Kind: kind, Card: w[2], Model: unword(w[3]), Tenant: unword(w[4]), For: unword(w[5])})
		case w[0] == "out" && len(w) >= 2:
			out.Tenants = append(out.Tenants, w[1])
			if len(w) > 2 {
				out.Models[w[1]] = w[2:]
			}
		default:
			panic("the Lean scheduler answered " + line)
		}
	}
	return acts, out
}

// decideRound is the scheduler the driver runs: here, the Lean model.
func decideRound(cards []Card, flows []Flow, slots map[string]int, lines Lines, now time.Time, pol Policy) ([]Action, Lines) {
	return DecideLean(cards, flows, slots, lines, now, pol)
}
