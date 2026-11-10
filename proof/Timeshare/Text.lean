/-
The model's arguments and answers as text: what `Check.lean` reads from
the Go tests. (Only that: the program calls the model through
`Export.lean`, and so do the cases here.)

One round:

    case NOW MAXTIMESLICE LOADRATIO IDLE
    card ID STATE MODEL OWNER NEXT INFLIGHT TURNAT BUSYAT LOAD     ("-": none)
    flow TENANT MODEL QUEUED OLDEST
    slot MODEL N
    line TENANT MODELS...            the lines before, in order
    act KIND CARD MODEL TENANT FOR   what was decided, in order
    out TENANT MODELS...             the lines after

(It imports only the model: Mathlib has no objects to link against.)
-/
import Timeshare.Export

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

/-- What the model decides for the case: the actions, and the lines after.
Through `Export.decideRound`, as the program calls it. -/
def Case.decide (c : Case) : List String × List (String × List String) :=
  let d := Export.decideRound c.cards.toArray c.flows.toArray c.slots.toArray
    (c.lines.map fun p => (p.1, p.2.toArray)).toArray c.now.toUInt64 c.pol
  (d.actions.toList.map showAct, d.lines.toList.map fun p => (p.1, p.2.toList))

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
  let queues := (c.tenants.map fun p => (p.1, p.2.1, (p.2.2.map (·.2)).toArray)).toArray
  let p := Export.roundRobinQueues queues c.own c.after c.n.toUInt64
  let id (r : Export.Req) : String := match c.tenants[r.queue]? with
    | some t => match t.2.2[r.index]? with
      | some q => q.1
      | none => "?"
    | none => "?"
  (p.requests.toList.map id, p.last)

end Timeshare.Text
