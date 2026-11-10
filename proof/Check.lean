/-
`timeshare-check CASES`: the Lean model against the Go code.

CASES is what `TIMESHARE_CASES=file go test ./internal/sched -run TestCases`
writes: every call of Go's `Decide` in a few hundred simulated worlds, with
what it answered. This runs `Timeshare.decide` on the same arguments and
fails if any answer differs, action for action and line for line.

One case:

    case NOW MAXTIMESLICE LOADRATIO IDLE
    card ID STATE MODEL OWNER NEXT INFLIGHT TURNAT BUSYAT LOAD     ("-": none)
    flow TENANT MODEL QUEUED OLDEST
    slot MODEL N
    line TENANT MODELS...            the lines before, in order
    act KIND CARD MODEL TENANT FOR   what Go decided, in order
    out TENANT MODELS...             the lines after
    end

(It imports only the model: Mathlib has no objects to link against.)
-/
import Timeshare.Text

open Timeshare Timeshare.Text

/-- What Lean decides for the case, and whether Go decided the same. -/
def check (c : Case) : Option String :=
  let (acts, out) := c.decide
  if acts = c.acts ∧ out = c.out then none
  else some s!"at {c.now}: go decided {c.acts}, lines {c.out}; lean decided {acts}, lines {out}"

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: timeshare-check CASES"; return 2
  let mut cur : Case := {}
  let mut rr : RRCase := {}
  let mut calls := 0
  let mut n := 0
  let mut acts := 0
  let mut bad := 0
  for line in ← IO.FS.lines path do
    let ws := (line.splitOn " ").filter (· ≠ "")
    if ws = ["end"] ∧ rr.active then
      calls := calls + 1
      let got := rr.run
      if got ≠ (rr.picks, rr.last) then
        bad := bad + 1
        if bad ≤ 5 then IO.eprintln s!"RoundRobin call {calls}: go picked {rr.picks} (last {rr.last}), lean {got.1} (last {got.2})"
      rr := {}
    else if ws = ["end"] then
      n := n + 1
      acts := acts + cur.acts.length
      if let some why := check cur then
        bad := bad + 1
        if bad ≤ 5 then IO.eprintln s!"case {n} {why}"
      cur := {}
    else if ws.head? ∈ [some "rr", some "rt", some "rp", some "rl"] then
      match rr.add ws with
      | .ok c => rr := c
      | .error e => IO.eprintln e; return 2
    else if ws ≠ [] then
      match cur.add ws with
      | .ok c => cur := c
      | .error e => IO.eprintln e; return 2
  IO.println s!"timeshare-check: {n} rounds, {acts} decisions, {calls} calls of RoundRobin, {bad} where lean and go differ"
  return if bad = 0 ∧ n > 0 ∧ calls > 0 then 0 else 1

