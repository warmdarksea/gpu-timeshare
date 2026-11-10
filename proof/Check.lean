/-
`timeshare-check CASES`: the Lean model against the Go code.

CASES is what `TIMESHARE_CASES=file go test ./internal/sched -run TestCases`
writes: every call of Go's `Decide` in a few hundred simulated worlds, with
what it answered. This runs `Timeshare.decide` on the same arguments and
fails if any answer differs, action for action and line for line.

One case:

    case NOW MAXTIMESLICE LOADRATIO IDLE
    card ID STATE MODEL OWNER INFLIGHT TURNAT BUSYAT LOAD     ("-": none)
    flow TENANT MODEL QUEUED OLDEST
    slot MODEL N
    line TENANT MODELS...            the lines before, in order
    act KIND CARD MODEL TENANT       what Go decided, in order
    out TENANT MODELS...             the lines after
    end

(It imports only the model: Mathlib has no objects to link against.)
-/
import Timeshare.Policy

open Timeshare

abbrev W := World String String String

structure Case where
  now : Nat := 0
  pol : Policy := { maxTimeslice := 0 }
  cards : List (Card String String String) := []
  flows : List (Flow String String) := []
  slots : List (String × Nat) := []
  lines : List (String × List String) := []
  acts : List String := []
  out : List (String × List String) := []

def opt (s : String) : Option String := if s = "-" then none else some s
def unopt : Option String → String
  | some s => s
  | none => "-"

def parseSt : String → St
  | "starting" => .starting
  | "up" => .up
  | "draining" => .draining
  | _ => .down

def showKind : Kind → String
  | .start => "start"
  | .stop => "stop"
  | .drain => "drain"
  | .pass => "pass"

def showAct (a : Action String String String) : String :=
  s!"{showKind a.kind} {a.card} {unopt a.model} {unopt a.tenant}"

def toLines (l : List (String × List String)) : Lines String String :=
  { tenants := l.map (·.1)
    models := fun t => match l.find? (·.1 = t) with
      | some p => p.2
      | none => [] }

def fromLines (l : Lines String String) : List (String × List String) :=
  l.tenants.map fun t => (t, l.models t)

/-- One line of the file into the case being read. -/
def Case.add (c : Case) (ws : List String) : Except String Case :=
  match ws with
  | ["case", now, q, r, i] =>
    pure { c with now := now.toNat!, pol := { maxTimeslice := q.toNat!, loadRatio := r.toNat!, idle := i.toNat! } }
  | ["card", id, st, m, o, infl, turn, busy, load] =>
    let card : Card String String String :=
      { id := id, st := parseSt st, model := opt m, owner := opt o, inflight := infl.toNat!,
        turnAt := turn.toNat!, busyAt := busy.toNat!, load := load.toNat! }
    pure { c with cards := c.cards ++ [card] }
  | ["flow", t, m, n, old] =>
    pure { c with flows := c.flows ++ [{ tenant := t, model := m, queued := n.toNat!, oldest := old.toNat! }] }
  | ["slot", m, n] => pure { c with slots := c.slots ++ [(m, n.toNat!)] }
  | "line" :: t :: ms => pure { c with lines := c.lines ++ [(t, ms)] }
  | ["act", k, card, m, t] => pure { c with acts := c.acts ++ [s!"{k} {card} {m} {t}"] }
  | "out" :: t :: ms => pure { c with out := c.out ++ [(t, ms)] }
  | _ => throw ("can't read: " ++ " ".intercalate ws)

/-- What Lean decides for the case, and whether Go decided the same. -/
def Case.check (c : Case) : Option String :=
  let slots (m : String) : Nat := match c.slots.find? (·.1 = m) with
    | some p => p.2
    | none => 0
  let (as, l) := decide c.cards c.flows slots (toLines c.lines) c.now c.pol
  let acts := as.map showAct
  let out := fromLines l
  if acts = c.acts ∧ out = c.out then none
  else some s!"at {c.now}: go decided {c.acts}, lines {c.out}; lean decided {acts}, lines {out}"

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: timeshare-check CASES"; return 2
  let mut cur : Case := {}
  let mut n := 0
  let mut acts := 0
  let mut bad := 0
  for line in ← IO.FS.lines path do
    let ws := (line.splitOn " ").filter (· ≠ "")
    if ws = ["end"] then
      n := n + 1
      acts := acts + cur.acts.length
      if let some why := cur.check then
        bad := bad + 1
        if bad ≤ 5 then IO.eprintln s!"case {n} {why}"
      cur := {}
    else if ws ≠ [] then
      match cur.add ws with
      | .ok c => cur := c
      | .error e => IO.eprintln e; return 2
  IO.println s!"timeshare-check: {n} rounds, {acts} decisions, {bad} where lean and go differ"
  return if bad = 0 ∧ n > 0 then 0 else 1
