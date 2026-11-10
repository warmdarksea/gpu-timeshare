/-
gpu-timeshare's scheduling algorithm, in Lean: which model is on which
card, whose turn it is, and when a turn ends.

This file is `internal/sched/policy.go`'s `Decide` again, function for
function ([Name] is the rule there, and the action in `spec/Turns.tla`).
`doc/VERIFICATION.md` §2 is the same thing in English. It is executable:
`Check.lean` runs it against the Go code's own decisions. It imports
nothing, so that an executable can link it; the proofs about it (which
want Mathlib) are in `Timeshare/Proofs`.

The words. A flow is one tenant's queued requests for one model. A card
holds one model at a time and its time is cut into turns; a turn belongs
to a tenant. Tenants with queued requests stand in a line, and each keeps
a line of its own models; the first has waited longest. A model is lost
when it has queued requests and is on no card, short when it is on a card
and has more queued than its cards can take.
-/

namespace Timeshare

/-- What a card is doing. Draining: finishing what is in flight, taking
nothing new, then it stops. -/
inductive St where
  | down | starting | up | draining
  deriving DecidableEq, Repr, Inhabited

/-- One GPU, as the policy sees it. Times are in any one unit. -/
structure Card (T M C : Type) where
  id : C
  st : St := .down
  /-- what is on it (`none` when down) -/
  model : Option M := none
  /-- the tenant whose turn it is -/
  owner : Option T := none
  /-- what it drains for, or has drained for: the model it loads next, for
  `owner` (`none`: nothing) -/
  next : Option M := none
  /-- requests being answered on it -/
  inflight : Nat := 0
  /-- when this turn began: the load finished, or the turn passed -/
  turnAt : Nat := 0
  /-- the last time it had work -/
  busyAt : Nat := 0
  /-- how long the model took to load -/
  load : Nat := 0

/-- One tenant's queued requests for one model (not the ones in flight). -/
structure Flow (T M : Type) where
  tenant : T
  model : M
  queued : Nat
  /-- its oldest queued request: newcomers join the lines in this order -/
  oldest : Nat

/-- What the scheduler remembers between rounds: who has waited longest.
`tenants` is the tenants with queued requests, `models t` tenant `t`'s
models with queued requests; the first is served first. -/
structure Lines (T M : Type) where
  tenants : List T := []
  models : T → List M := fun _ => []

structure Policy where
  /-- a turn can't be taken before it is this old -/
  maxTimeslice : Nat
  /-- nor before it is this many times the model's load time -/
  loadRatio : Nat := 0
  /-- an idle card stops after this long (0: never) -/
  idle : Nat := 0

inductive Kind where
  /-- load `model` on `card`; the turn is `tenant`'s -/
  | start
  /-- stop what is on `card` -/
  | stop
  /-- send `card` no more requests; it stops once it has finished -/
  | drain
  /-- the turn on `card` is `tenant`'s now -/
  | pass
  deriving DecidableEq, Repr

structure Action (T M C : Type) where
  kind : Kind
  card : C
  model : Option M := none
  tenant : Option T := none
  /-- `drain`: the model the card drains for -/
  next : Option M := none

/-- Everything a round sees: `Decide`'s arguments. A rule that applies
changes the cards and the lines, and the next rule sees the change. -/
structure World (T M C : Type) where
  cards : List (Card T M C)
  flows : List (Flow T M)
  /-- how many requests each model answers at once on one card -/
  slots : M → Nat
  lines : Lines T M
  now : Nat
  pol : Policy

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

/-! ## The lines -/

/-- Move `x` to the end of `s`, if it is there. -/
def toBack {α : Type} [DecidableEq α] (s : List α) (x : α) : List α :=
  if x ∈ s then s.erase x ++ [x] else s

/-- A tenant goes to the back of the line. -/
def Lines.tenantToBack (l : Lines T M) (t : Option T) : Lines T M :=
  match t with
  | some t => { l with tenants := toBack l.tenants t }
  | none => l

/-- The end of a turn: its tenant goes to the back of the line, and its
model to the back of every tenant's (they all had it). -/
def Lines.ended (l : Lines T M) (t : Option T) (m : Option M) : Lines T M :=
  let l := l.tenantToBack t
  match m with
  | some m => { l with models := fun u => toBack (l.models u) m }
  | none => l

/-- The lines for these flows: whoever has nothing queued any more leaves,
and newcomers join at the back, the one with the oldest request first. -/
def Lines.join (l : Lines T M) (flows : List (Flow T M)) : Lines T M :=
  let fs := (flows.mergeSort fun a b => a.oldest ≤ b.oldest).filter fun f => f.queued > 0
  let has (t : T) : Bool := fs.any fun f => f.tenant = t
  let hasFlow (t : T) (m : M) : Bool := fs.any fun f => f.tenant = t ∧ f.model = m
  let old (t : T) : List M := if t ∈ l.tenants then l.models t else []
  { tenants := (l.tenants.filter has ++ fs.map (·.tenant)).eraseDups
    models := fun t =>
      ((old t).filter (hasFlow t) ++ (fs.filter fun f => f.tenant = t).map (·.model)).eraseDups }

/-! ## What the rules ask about the world -/

/-- The card has a model that is loading or up (not one that is leaving). -/
def Card.serving (c : Card T M C) : Bool := c.st = .starting || c.st = .up

/-- The card is somebody's: their model is loading or up there, or it
drains (or has drained) for them. -/
def Card.taken (c : Card T M C) : Bool := c.serving || c.next.isSome

/-- The card has `m`, or will: it drains (or has drained) for it. -/
def Card.has (c : Card T M C) (m : M) : Bool := if c.serving then c.model = some m else c.next = some m

/-- How old a turn on `c` must be before somebody else can have the card. -/
def Policy.quantum (p : Policy) (c : Card T M C) : Nat :=
  max p.maxTimeslice (p.loadRatio * c.load)

/-- How many requests tenant `t` has queued for model `m`. -/
def World.queued (w : World T M C) (t : T) (m : M) : Nat :=
  (w.flows.filter fun f => f.tenant = t ∧ f.model = m).foldl (· + ·.queued) 0

/-- How many requests tenant `t` has queued for what is on a card. -/
def World.queuedOn (w : World T M C) (t : T) (m : Option M) : Nat :=
  match m with
  | some m => w.queued t m
  | none => 0

/-- How many requests are queued for model `m`, anybody's. -/
def World.work (w : World T M C) (m : M) : Nat :=
  (w.flows.filter fun f => f.model = m).foldl (· + ·.queued) 0

/-- How many cards have a turn of `t`'s. -/
def World.held (w : World T M C) (t : T) : Nat :=
  (w.cards.filter fun c => c.taken && c.owner = some t).length

def World.heldBy (w : World T M C) (t : Option T) : Nat :=
  match t with
  | some t => w.held t
  | none => 0

/-- `m` is on a card (loading or up). -/
def World.placed (w : World T M C) (m : M) : Bool :=
  w.cards.any fun c => c.has m

/-- How many more requests `m`'s cards can take (a card that drains for
`m` will take a card's worth). -/
def World.room (w : World T M C) (m : M) : Nat :=
  w.cards.foldl (fun n c =>
    if c.serving then (if c.model = some m then n + (w.slots m - c.inflight) else n)
    else if c.next = some m then n + w.slots m
    else n) 0


/-- `t`'s first model that has queued requests and is on no card. -/
def World.lost (w : World T M C) (t : T) : Option M :=
  (w.lines.models t).find? fun m => !w.placed m

def World.anyLost (w : World T M C) : Bool :=
  w.lines.tenants.any fun t => (w.lost t).isSome

/-- `t`'s first model, other than `except`, that is on a card and has more
queued than its cards can take. -/
def World.short (w : World T M C) (t : T) (except : Option M) : Option M :=
  (w.lines.models t).find? fun m => some m ≠ except && w.placed m && w.work m > w.room m

/-- The card is up with nothing queued or in flight, and has been for at
least `d`. -/
def World.idleFor (w : World T M C) (d : Nat) (c : Card T M C) : Bool :=
  c.st = .up && c.inflight = 0 && (match c.model with | some m => w.work m = 0 | none => true)
    && w.now - c.busyAt ≥ d

/-- The first of the positions in `l` that `better` prefers to all before it. -/
def firstBest {α : Type} (l : List (Nat × α)) (better : α → α → Bool) : Option (Nat × α) :=
  l.foldl (fun best x =>
    match best with
    | none => some x
    | some b => if better x.2 b.2 then some x else some b) none

/-- The card (and its position) that has been idle for at least `d`, and
for longest. -/
def World.longestIdle (w : World T M C) (d : Nat) : Option (Nat × Card T M C) :=
  firstBest (w.cards.zipIdx.map (fun p => (p.2, p.1)) |>.filter fun p => w.idleFor d p.2)
    fun c b => c.busyAt < b.busyAt

/-- Go down a line and keep the best: the first of the lowest `rank` among
those who have a pick, with that pick. (Go's loops in `winner` and `claim`:
a later tenant replaces the best so far only if its rank is strictly
lower.) -/
def firstLowest {α β : Type} (pick : α → Option β) (rank : α → Nat) (l : List α) : Option (α × β) :=
  l.foldl (fun best t =>
    match pick t, best with
    | some m, none => some (t, m)
    | some m, some b => if rank t < rank b.1 then some (t, m) else some b
    | none, _ => best) none

/-- What tenant `t` would have on card `c`, whose turn is a quantum old: it
may move a lost model there, stay (it has queued requests for the model
that is there), or copy a short model there if it would still hold fewer
cards than the owner afterwards. It moves if it can, else stays, else
copies. -/
def World.pick (w : World T M C) (c : Card T M C) (t : T) : Option M :=
  match w.lost t with
  | some m => some m                                             -- move
  | none =>
    if w.queuedOn t c.model > 0 then c.model                    -- stay
    else if some t ≠ c.owner ∧ w.held t + 2 ≤ w.heldBy c.owner then w.short t c.model  -- copy
    else none

/-- Fewest cards first; the owner of `c`, who has had its turn, counts one
card fewer and comes last among equals. -/
def World.rank (w : World T M C) (c : Card T M C) (t : T) : Nat :=
  if some t = c.owner then 2 * (w.held t - 1) + 1 else 2 * w.held t

/-- The tenant with the best claim to `c`, whose turn is a quantum old, and
the model it would have there: fewest cards first, then the line. (`none`
if the turn is younger, or began this instant: a turn that has just passed
can't pass again, so a round ends even with a quantum of zero.) -/
def World.winner (w : World T M C) (c : Card T M C) : Option (T × M) :=
  if c.st ≠ .up ∨ w.now - c.turnAt < w.pol.quantum c ∨ w.now ≤ c.turnAt then none
  else firstLowest (w.pick c) (w.rank c) w.lines.tenants

/-- Who gets a free card, and for which model: the first tenant with a
lost model or a short one (fewest cards first, then the line), and its
first lost model, else its first short one. -/
def World.claim (w : World T M C) : Option (T × M) :=
  firstLowest (fun t => (w.lost t).orElse fun _ => w.short t none) w.held w.lines.tenants

/-! ## The rules -/

/-- Stop the card at position `i`: the end of its turn. -/
def World.stop (w : World T M C) (i : Nat) (c : Card T M C) : Action T M C × World T M C :=
  ({ kind := .stop, card := c.id, model := c.model },
   { w with cards := w.cards.set i { id := c.id }, lines := w.lines.ended c.owner c.model })

/-- The first rule that has something to do, and the world after it. -/
def World.rule (w : World T M C) : Option (Action T M C × World T M C) :=
  let cards := w.cards.zipIdx.map fun p => (p.2, p.1)
  -- [Drained] a draining card with nothing in flight stops; it stays its next tenant's
  match cards.find? fun p => p.2.st = .draining && p.2.inflight = 0 with
  | some (i, c) =>
    some ({ kind := .stop, card := c.id, model := c.model },
          { w with cards := w.cards.set i { id := c.id, owner := c.owner, next := c.next } })
  | none =>
  -- [Start] a card that drained for somebody loads their model
  match cards.find? fun p => p.2.st = .down && p.2.next.isSome with
  | some (i, c) =>
    some ({ kind := .start, card := c.id, model := c.next, tenant := c.owner },
          { w with cards := w.cards.set i { id := c.id, st := .starting, model := c.next, owner := c.owner } })
  | none =>
  let free := cards.find? fun p => p.2.st = .down && p.2.next.isNone
  -- [Start] a free card goes to the first claim
  match w.claim, free with
  | some (t, m), some (i, c) =>
    some ({ kind := .start, card := c.id, model := some m, tenant := some t },
          { w with cards := w.cards.set i { id := c.id, st := .starting, model := some m, owner := some t } })
  | _, _ =>
  -- [GiveWay] no card is free and a model is lost: the card idle longest stops
  match (if free.isNone && w.anyLost then w.longestIdle 0 else none) with
  | some (i, c) => some (w.stop i c)
  | none =>
  -- [IdleStop] a card idle for `idle` stops
  match (if w.pol.idle > 0 then w.longestIdle w.pol.idle else none) with
  | some (i, c) => some (w.stop i c)
  | none =>
  -- [Pass] the best claim wants the model that is there: the turn changes hands
  match cards.findSome? fun p =>
      match w.winner p.2 with
      | some (t, m) => if some t ≠ p.2.owner ∧ some m = p.2.model then some (p, t, m) else none
      | none => none with
  | some ((i, c), t, m) =>
    some ({ kind := .pass, card := c.id, model := some m, tenant := some t },
          { w with cards := w.cards.set i { c with owner := some t, turnAt := w.now }
                   lines := w.lines.tenantToBack c.owner })
  | none =>
  -- [Drain] it wants another model: the old turn is over, and the card is the winner's from
  -- now, for that model. From the owner with the most cards, the oldest turn first.
  let wanted := cards.filterMap fun p =>
    match w.winner p.2 with
    | some (t, m) => if some m ≠ p.2.model then some (p.1, (p.2, t, m)) else none
    | none => none
  match firstBest wanted (fun x y =>
      w.heldBy x.1.owner > w.heldBy y.1.owner ||
        (w.heldBy x.1.owner = w.heldBy y.1.owner && x.1.turnAt < y.1.turnAt)), free with
  | some (i, (c, t, m)), none =>
    some ({ kind := .drain, card := c.id, model := c.model, tenant := some t, next := some m },
          { w with cards := w.cards.set i { c with st := .draining, owner := some t, next := some m }
                   lines := w.lines.ended c.owner c.model })
  | _, _ => none


/-- Apply rules until none applies, at most `fuel` times. -/
def World.run (w : World T M C) : Nat → List (Action T M C) × World T M C
  | 0 => ([], w)
  | fuel + 1 =>
    match w.rule with
    | none => ([], w)
    | some (a, w') => let (as, w'') := w'.run fuel; (a :: as, w'')

/-- One round of the scheduling algorithm: what to do with the cards now,
and the lines as they are afterwards. A round is at most three decisions a
card (it drains, stops and starts), so the fuel is never what ends it. -/
def decide (cards : List (Card T M C)) (flows : List (Flow T M)) (slots : M → Nat) (lines : Lines T M)
    (now : Nat) (pol : Policy) : List (Action T M C) × Lines T M :=
  let w : World T M C := { cards, flows, slots, lines := lines.join flows, now, pol }
  let (as, w') := w.run (3 * cards.length + 1)
  (as, w'.lines)

end Timeshare
