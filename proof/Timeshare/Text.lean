/-
The model's arguments and answer as text: what `Check.lean` reads from the
Go tests, and what the Go program hands `timeshare_decide` and
`timeshare_roundrobin`: the Lean model is its scheduler
(internal/sched/lean.go).

One round:

    case NOW MAXTIMESLICE LOADRATIO IDLE
    card ID STATE MODEL OWNER NEXT INFLIGHT TURNAT BUSYAT LOAD     ("-": none)
    flow TENANT MODEL QUEUED OLDEST
    slot MODEL N
    line TENANT MODELS...            the lines before, in order

and the answer:

    act KIND CARD MODEL TENANT FOR   in order
    out TENANT MODELS...             the lines after

(It imports only the model: Mathlib has no objects to link against.)
-/
import Timeshare.Policy

namespace Timeshare.Text

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
  s!"{showKind a.kind} {a.card} {unopt a.model} {unopt a.tenant} {unopt a.next}"

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
  | ["card", id, st, m, o, nx, infl, turn, busy, load] =>
    let card : Card String String String :=
      { id := id, st := parseSt st, model := opt m, owner := opt o, next := opt nx, inflight := infl.toNat!,
        turnAt := turn.toNat!, busyAt := busy.toNat!, load := load.toNat! }
    pure { c with cards := c.cards ++ [card] }
  | ["flow", t, m, n, old] =>
    pure { c with flows := c.flows ++ [{ tenant := t, model := m, queued := n.toNat!, oldest := old.toNat! }] }
  | ["slot", m, n] => pure { c with slots := c.slots ++ [(m, n.toNat!)] }
  | "line" :: t :: ms => pure { c with lines := c.lines ++ [(t, ms)] }
  | ["act", k, card, m, t, nx] => pure { c with acts := c.acts ++ [s!"{k} {card} {m} {t} {nx}"] }

  | "out" :: t :: ms => pure { c with out := c.out ++ [(t, ms)] }
  | _ => throw ("can't read: " ++ " ".intercalate ws)

/-- What the model decides for the case: the actions, and the lines after. -/
def Case.decide (c : Case) : List String × List (String × List String) :=
  let slots (m : String) : Nat := match c.slots.find? (·.1 = m) with
    | some p => p.2
    | none => 0
  let (as, l) := Timeshare.decide c.cards c.flows slots (toLines c.lines) c.now c.pol
  (as.map showAct, fromLines l)

/-- A round as text in, the answer as text out: `Decide`, for a program
that is not written in Lean. A line it cannot read is answered with
`error ...` and nothing else. -/
@[export timeshare_decide]
def decideText (input : String) : String :=
  let lines := (input.splitOn "\n").map fun l => (l.splitOn " ").filter (· ≠ "")
  match lines.foldlM (fun (c : Case) ws => if ws = [] then pure c else c.add ws) {} with
  | .error e => "error " ++ e ++ "\n"
  | .ok c =>
    let (acts, out) := c.decide
    String.join (acts.map fun a => "act " ++ a ++ "\n") ++
      String.join (out.map fun p => "out " ++ " ".intercalate (p.1 :: p.2) ++ "\n")

/-- A call of `RoundRobin`, and what Go picked:

    rr AFTER N OWNER HELD SLOTS
    rt TENANT INFLIGHT ID:KEY...     each tenant's requests, the tenants in order
    rp ID                            the picks, in order
    rl LAST
-/
structure RRCase where
  active : Bool := false
  after : Option String := none
  n : Nat := 0
  own : Owner String := {}
  tenants : List (String × Nat × List (String × String)) := []
  picks : List String := []
  last : Option String := none

def RRCase.add (c : RRCase) (ws : List String) : Except String RRCase :=
  match ws with
  | ["rr", after, n, o, held, slots] =>
    pure { c with active := true, after := opt after, n := n.toNat!,
                  own := { tenant := opt o, held := held.toNat!, slots := slots.toNat! } }
  | "rt" :: t :: infl :: rs =>
    let reqs := rs.map fun r => match r.splitOn ":" with
      | [id, k] => (id, k)
      | _ => (r, r)
    pure { c with tenants := c.tenants ++ [(t, infl.toNat!, reqs)] }
  | ["rp", id] => pure { c with picks := c.picks ++ [id] }
  | ["rl", last] => pure { c with last := opt last }
  | _ => throw ("can't read: " ++ " ".intercalate ws)

/-- What the model picks: the requests' ids, and the tenant served last. -/
def RRCase.run (c : RRCase) : List String × Option String :=
  let inflight (t : String) : Nat := match c.tenants.find? (·.1 = t) with
    | some p => p.2.1
    | none => 0
  let (picked, last) := roundRobin (c.tenants.map fun p => (p.1, p.2.2)) (fun r : String × String => r.2)
    (fun a b => a ≤ b) inflight c.own c.after c.n
  (picked.map (·.1), last)

/-- A call of `RoundRobin` as text in (`rr`, `rt`), the picks as text out
(`rp`, `rl`): for a program that is not written in Lean. -/
@[export timeshare_roundrobin]
def roundRobinText (input : String) : String :=
  let lines := (input.splitOn "\n").map fun l => (l.splitOn " ").filter (· ≠ "")
  match lines.foldlM (fun (c : RRCase) ws => if ws = [] then pure c else c.add ws) {} with
  | .error e => "error " ++ e ++ "\n"
  | .ok c =>
    let (picks, last) := c.run
    String.join (picks.map fun p => "rp " ++ p ++ "\n") ++ "rl " ++ unopt last ++ "\n"

end Timeshare.Text
