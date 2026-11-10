/-
The scheduler as C functions: what a program that is not written in Lean
calls. Every definition here with `@[export lean_ts_...]` is a C symbol of
that name.

It is the model's own interface, with names for tenants, models and cards
(`String`), and with the types C has where the model's would have to be
built by hand: `UInt64` for `Nat`, `UInt8` for `St` and `Kind`, `Array` for
`List`, an array of pairs for a function. So:

- a constructor for each structure that goes in (`lean_ts_card`,
  `lean_ts_flow`, `lean_ts_policy`, ...), from numbers and strings;
- `lean_ts_decide` and `lean_ts_round_robin`: `decide` and `roundRobin`;
- a projection for each field of what comes out (`lean_ts_action_kind`,
  ...). Lean lets an exported function borrow nothing: every argument,
  a projection's too, is consumed (so `lean_inc` what is read twice), and
  every object returned is the caller's to release.

Nothing outside Lean needs to know how a structure is laid out: C handles
strings and arrays through `lean.h`, and everything else through these.
ffi/schedule.c wraps them in C structs; that is what the Go program links.

(It imports only the model: Mathlib has no objects to link against.)
-/
import Timeshare.Policy

namespace Timeshare.Export

open Timeshare

abbrev ECard := Card String String String
abbrev EFlow := Flow String String
abbrev EAction := Action String String String
/-- A tenant and its models, in order: one entry of the lines. -/
abbrev ELine := String × Array String

/-! ## Values going in -/

/-- `some s`, or `none` (and `s` is not looked at). -/
@[export lean_ts_opt]
def opt (has : Bool) (s : String) : Option String := if has then some s else none

/-- 0 down, 1 starting, 2 up, 3 draining. -/
def stOf (n : UInt8) : St :=
  if n = 1 then .starting else if n = 2 then .up else if n = 3 then .draining else .down

@[export lean_ts_card]
def card (id : String) (st : UInt8) (model owner next : Option String)
    (inflight turnAt busyAt load : UInt64) : ECard :=
  { id, st := stOf st, model, owner, next, inflight := inflight.toNat, turnAt := turnAt.toNat,
    busyAt := busyAt.toNat, load := load.toNat }

@[export lean_ts_flow]
def flow (tenant model : String) (queued oldest : UInt64) : EFlow :=
  { tenant, model, queued := queued.toNat, oldest := oldest.toNat }

/-- How many requests `model` answers at once on one card. -/
@[export lean_ts_slots]
def slots (model : String) (n : UInt64) : String × Nat := (model, n.toNat)

@[export lean_ts_line]
def line (tenant : String) (models : Array String) : ELine := (tenant, models)

@[export lean_ts_policy]
def policy (maxTimeslice loadRatio idle : UInt64) : Policy :=
  { maxTimeslice := maxTimeslice.toNat, loadRatio := loadRatio.toNat, idle := idle.toNat }

/-! ## `decide` -/

def toLines (l : Array ELine) : Lines String String :=
  { tenants := l.toList.map (·.1)
    models := fun t => match l.find? (·.1 = t) with
      | some p => p.2.toList
      | none => [] }

def fromLines (l : Lines String String) : Array ELine :=
  (l.tenants.map fun t => (t, (l.models t).toArray)).toArray

/-- What a round decides: the actions, in order, and the lines afterwards. -/
structure Decision where
  actions : Array EAction
  lines : Array ELine

/-- `Timeshare.decide`. A model with no entry in `slots` has none. -/
@[export lean_ts_decide]
def decideRound (cards : Array ECard) (flows : Array EFlow) (slots : Array (String × Nat))
    (lines : Array ELine) (now : UInt64) (pol : Policy) : Decision :=
  let slotsOf (m : String) : Nat := match slots.find? (·.1 = m) with
    | some p => p.2
    | none => 0
  let (as, l) := Timeshare.decide cards.toList flows.toList slotsOf (toLines lines) now.toNat pol
  { actions := as.toArray, lines := fromLines l }

@[export lean_ts_decision_actions]
def decisionActions (d : Decision) : Array EAction := d.actions

@[export lean_ts_decision_lines]
def decisionLines (d : Decision) : Array ELine := d.lines

/-- 0 start, 1 stop, 2 drain, 3 pass. -/
def kindCode : Kind → UInt8
  | .start => 0
  | .stop => 1
  | .drain => 2
  | .pass => 3

@[export lean_ts_action_kind]
def actionKind (a : EAction) : UInt8 := kindCode a.kind

@[export lean_ts_action_card]
def actionCard (a : EAction) : String := a.card

@[export lean_ts_action_model]
def actionModel (a : EAction) : Option String := a.model

@[export lean_ts_action_tenant]
def actionTenant (a : EAction) : Option String := a.tenant

@[export lean_ts_action_next]
def actionNext (a : EAction) : Option String := a.next

@[export lean_ts_line_tenant]
def lineTenant (l : ELine) : String := l.1

@[export lean_ts_line_models]
def lineModels (l : ELine) : Array String := l.2

@[export lean_ts_opt_is_some]
def optIsSome (o : Option String) : Bool := o.isSome

/-- The string of `some`; of `none`, the empty one. -/
@[export lean_ts_opt_get]
def optGet (o : Option String) : String := o.getD ""

/-! ## `roundRobin` -/

/-- One tenant's queued requests for the model: the tenant, how many of its
requests are in flight, and the key of each queued one, in order. -/
abbrev Queue := String × Nat × Array String

@[export lean_ts_queue]
def queue (tenant : String) (inflight : UInt64) (keys : Array String) : Queue :=
  (tenant, inflight.toNat, keys)

@[export lean_ts_owner]
def owner (tenant : Option String) (held slots : UInt64) : Owner String :=
  { tenant, held := held.toNat, slots := slots.toNat }

/-- A queued request: which queue it is in, where in it, and its key. -/
structure Req where
  queue : Nat
  index : Nat
  key : String

/-- The requests picked, in order, and the tenant served last. -/
structure Picks where
  requests : Array Req
  last : Option String

/-- `Timeshare.roundRobin`. The queues come in the order of their tenants'
names. -/
@[export lean_ts_round_robin]
def roundRobinQueues (queues : Array Queue) (own : Owner String) (after : Option String) (n : UInt64) : Picks :=
  let inflight (t : String) : Nat := match queues.find? (·.1 = t) with
    | some q => q.2.1
    | none => 0
  let byTenant := queues.toList.zipIdx.map fun (q, i) =>
    (q.1, q.2.2.toList.zipIdx.map fun (k, j) => ({ queue := i, index := j, key := k } : Req))
  let (picked, last) := Timeshare.roundRobin byTenant (fun r => r.key) (fun a b => a ≤ b) inflight own after n.toNat
  { requests := picked.toArray, last }

@[export lean_ts_picks_requests]
def picksRequests (p : Picks) : Array Req := p.requests

@[export lean_ts_picks_last]
def picksLast (p : Picks) : Option String := p.last

@[export lean_ts_req_queue]
def reqQueue (r : Req) : UInt64 := r.queue.toUInt64

@[export lean_ts_req_index]
def reqIndex (r : Req) : UInt64 := r.index.toUInt64

end Timeshare.Export
