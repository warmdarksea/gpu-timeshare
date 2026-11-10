/-
No starvation, on any number of cards, counted in turns: `mturns_bound`.

A turn *begins* when a free card is started on, when a turn passes from
one tenant to another, and when a card begins to drain for somebody (the
card is theirs from then on; the start that follows the drain is not a
new turn).

While tenant `t` has requests queued for model `m`, and until `m` is
started or a card drains for it, call a turn *charged* if it begins while
`t` holds no card (whoever it goes to), or is `t`'s own. At most
`K * N - 1` charged turns begin -- `N` the most tenants with queued
requests at a time, `K` the number of `t`'s models with queued requests
when the wait begins.

In words: while `t` holds no card, every card the scheduler hands out goes
to `t` or to a tenant that stood before `t` in the line and held none
either, and there are fewer than `N` of those; and every turn of `t`'s own
is for a model that stood before `m` in its line, or for `m`, and there
are fewer than `K` of those.

The system is the cards and the lines (`MSys`); a history (`MTrace`) is
rounds of `decide` on all the cards, and between them whatever the model
servers do, each on its own card.
-/
import Timeshare.Proofs.MultiRule

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

section multi
variable (N : Nat) (t : T) (m : M)

/-- A card has drained for somebody and waits to be started. -/
def World.pending (w : World T M C) : Bool := w.cards.any fun c => c.st = .down && c.next.isSome

/-- A turn begins: a pass, a drain, or a start that is not the start of a
card that drained for somebody. -/
def begins (w : World T M C) (a : Action T M C) : Bool :=
  a.kind = .pass || a.kind = .drain || (a.kind = .start && !w.pending)

/-- A turn begins that is `t`'s own, or begins while `t` holds no card. -/
def charged (w : World T M C) (a : Action T M C) : Nat :=
  if begins w a = true ∧ (w.held t = 0 ∨ a.tenant = some t) then 1 else 0

/-- `m` is not started, and no card drains for it. -/
def Spares (a : Action T M C) : Prop :=
  (a.kind = .start → a.model ≠ some m) ∧ (a.kind = .drain → a.next ≠ some m)

/-- **One rule, on any number of cards**, while the flow waits and `m` is
not started: the flow still waits, and the measure is no higher -- one
lower if a charged turn began. -/
theorem rule_multi {w w' : World T M C} {a : Action T M C} (hw : MWaiting N t m w.cards w.lines)
    (h : w.rule = some (a, w')) (hno : Spares m a) :
    MWaiting N t m w'.cards w'.lines ∧
      mPot N t m w'.cards w'.lines + charged t w a ≤ mPot N t m w.cards w.lines := by
  have hlostm : w.placed m = false := not_placed_of_away m hw.away
  have hlost : (w.lost t).isSome = true := by
    unfold World.lost
    rw [List.find?_isSome]
    exact ⟨m, hw.model, by simp [hlostm]⟩
  cases rule_effect h with
  | drained i d hd hst _ =>
    obtain ⟨hw', he⟩ := mpot_congr N t m { id := d.id, owner := d.owner, next := d.next } hw hd
      (by intro v; simp [Card.taken, Card.serving, hst]) (by intro y; simp [Card.has, Card.serving, hst])
    exact ⟨hw', by simp [charged, begins, he]⟩
  | reserved i d hd hst hnext =>
    obtain ⟨hw', he⟩ := mpot_congr N t m { id := d.id, st := .starting, model := d.next, owner := d.owner, since := w.now } hw hd
      (by intro v; simp [Card.taken, Card.serving, hst, hnext]) (by intro y; simp [Card.has, Card.serving, hst])
    have hpend : w.pending = true := by
      unfold World.pending
      rw [List.any_eq_true]
      exact ⟨d, List.mem_of_getElem? hd, by simp [hst, hnext]⟩
    exact ⟨hw', by simp [charged, begins, hpend, he]⟩
  | start i d u x hd hst hnext hclaim hnone =>
    have hdt : d.taken = false := by simp [Card.taken, Card.serving, hst, hnext]
    have hxm : x ≠ m := fun hx => hno.1 rfl (by rw [hx])
    obtain ⟨hw', hA, hB, hC⟩ := mpot_start N t m (u := u) (x := x)
      (c' := { id := d.id, st := .starting, model := some x, owner := some u, since := w.now }) hw hd hdt
      (by simp [Card.taken, Card.serving]) rfl (by simp [Card.has, Card.serving])
      (by simp [Card.has, Card.serving, hxm])
    refine ⟨hw', ?_⟩
    have hpend : w.pending = false := by
      unfold World.pending
      rw [List.any_eq_false]
      intro c hc
      have := hnone c hc
      simpa using this
    have hbeg : begins w { kind := .start, card := d.id, model := some x, tenant := some u } = true := by
      simp [begins, hpend]
    unfold World.claim at hclaim
    by_cases hut : u = t
    · subst hut
      -- `t`'s own turn: it starts its first lost model, which stood before `m`
      obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp hlost
      have hpick := (firstLowest_some hclaim).2
      simp only [hx', Option.orElse_some, Option.some.injEq] at hpick
      subst hpick
      have hx0 : w.placed x' = false := lost_not_placed hx'
      have hxb : x' ∈ before (w.lines.models u) m := by
        unfold World.lost at hx'
        rcases find?_before hx' hw.model (by simp [hlostm]) with h1 | h1
        · exact absurd h1 hxm
        · exact h1
      have := hC rfl hxb hx0
      simp only [charged, hbeg, or_true, and_self, ite_true]
      exact this
    · by_cases h0 : w.held t = 0
      · -- `t` holds no card: the turn goes to somebody before it who holds none
        obtain ⟨hfirst, hu0⟩ := firstLowest_first (rank := w.held) hw.tenant
          (by obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp hlost; simp [hx']) h0 hclaim
        have hub : u ∈ before w.lines.tenants t := by
          rcases hfirst with h1 | h1
          · exact absurd h1 hut
          · exact h1
        have := hB hut h0 hub hu0
        simp only [charged, hbeg, h0, true_or, and_self, ite_true]
        exact this
      · have := hA hut
        have hne : ¬ (some u = some t) := fun h1 => hut (Option.some.inj h1)
        simp only [charged, h0, hne, or_self, and_false, ite_false, Nat.add_zero]
        exact this
  | stop i d dur hd hidle =>
    have hup := (idleFor_spec hidle).1
    have hs : d.serving = true := by simp [Card.serving, hup]
    obtain ⟨hw', he⟩ := mpot_ended N t m { id := d.id } hw hd hs (by simp [Card.taken, Card.serving])
    exact ⟨hw', by simpa [charged, begins] using he⟩
  | pass i d u mu hd hwin hown hmod =>
    have hup := (winner_old hwin).1
    have hs : d.serving = true := by simp [Card.serving, hup]
    have hdmem : d ∈ w.cards := List.mem_of_getElem? hd
    have hut : u ≠ t := by
      rintro rfl
      obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hlost
      have hmm := winner_lost hwin hm'
      subst hmm
      have h1 := lost_not_placed hm'
      have h2 : w.placed mu = true := by
        unfold World.placed
        rw [List.any_eq_true]
        exact ⟨d, hdmem, by simp [Card.has, hs, hmod.symm]⟩
      rw [h1] at h2
      cases h2
    obtain ⟨hw', hA, hB⟩ := mpot_pass N t m (c' := { d with owner := some u, turnAt := w.now }) hw hd
      (by simp [Card.taken, hs]) (by simp [Card.taken, Card.serving, hup]) rfl
      (by intro y; simp [Card.has, Card.serving, hup]) hut hown
    refine ⟨hw', ?_⟩
    by_cases h0 : w.held t = 0
    · have hot : some t ≠ d.owner := by
        intro h1
        have := heldIn_pos hdmem (by simp [Card.taken, hs]) h1.symm
        rw [← held_eq] at this
        omega
      obtain ⟨hfirst, hrank⟩ := winner_first hwin hw.tenant hlost hot h0
      have hub : u ∈ before w.lines.tenants t := by
        rcases hfirst with h1 | h1
        · exact absurd h1 hut
        · exact h1
      have hu0 : w.held u = 0 := by
        simp only [World.rank, hown, ite_false] at hrank
        omega
      have := hB h0 hub hu0
      simp only [charged, begins, h0, true_or, and_self, ite_true, decide_true, Bool.true_or]
      exact this
    · have hne : ¬ (some u = some t) := fun h1 => hut (Option.some.inj h1)
      simp only [charged, h0, hne, or_self, and_false, ite_false, Nat.add_zero]
      exact hA
  | drain i d u mu hd hwin hne =>
    -- the old turn ends, and the card is `u`'s from now, for `mu`
    have hup := (winner_old hwin).1
    have hs : d.serving = true := by simp [Card.serving, hup]
    have hdmem : d ∈ w.cards := List.mem_of_getElem? hd
    have hmum : mu ≠ m := fun hx => hno.2 rfl (by rw [hx])
    have hlt : i < w.cards.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hd
      cases hd
    obtain ⟨hw1, h1⟩ := mpot_ended N t m { id := d.id } hw hd hs (by simp [Card.taken, Card.serving])
    have hi1 : (w.cards.set i { id := d.id })[i]? = some ({ id := d.id } : Card T M C) := by
      simp [hlt]
    obtain ⟨hw2, hA, hB, hC⟩ := mpot_start N t m (u := u) (x := mu)
      (c' := { d with st := .draining, owner := some u, next := some mu, since := w.now }) hw1 hi1
      (by simp [Card.taken, Card.serving]) (by simp [Card.taken]) rfl
      (by simp [Card.has, Card.serving]) (by simp [Card.has, Card.serving, hmum])
    rw [List.set_set] at hw2 hA hB hC
    refine ⟨hw2, ?_⟩
    -- the cards in between: the old turn over, the new one not begun
    have hheld1 : ∀ v, heldIn (w.cards.set i { id := d.id }) v ≤ heldIn w.cards v := by
      intro v
      have := heldIn_set ({ id := d.id } : Card T M C) v hd
      simp only [Card.taken, Card.serving, reduceCtorEq, decide_false, Bool.or_self, Option.isSome_none,
        Bool.false_and, Bool.false_eq_true, ite_false] at this
      omega
    by_cases hut : u = t
    · subst hut
      obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp hlost
      have hmm := winner_lost hwin hx'
      subst hmm
      have hx0 : w.placed mu = false := lost_not_placed hx'
      have hxb : mu ∈ before (w.lines.models u) m := by
        unfold World.lost at hx'
        rcases find?_before hx' hw.model (by simp [hlostm]) with h2 | h2
        · exact absurd h2 hmum
        · exact h2
      -- still before `m`, and still on no card, once the old turn is over
      have hxb1 : mu ∈ before ((w.lines.ended d.owner d.model).models u) m := by
        cases hmod : d.model with
        | none => simpa using hxb
        | some x =>
          have hxm : x ≠ m := by
            have := hw.away d hdmem
            rw [has_of_serving hs, hmod] at this
            simpa using this
          have hmux : mu ≠ x := by
            rintro rfl
            have : w.placed mu = true := by
              unfold World.placed
              rw [List.any_eq_true]
              exact ⟨d, hdmem, by rw [has_of_serving hs, hmod]; simp⟩
            rw [hx0] at this
            cases this
          simp only [ended_models]
          rw [before_toBack (hw.nodup.2 u) hw.model hxm, List.mem_filter]
          exact ⟨hxb, by simpa using hmux⟩
      have hx01 : placedIn (w.cards.set i { id := d.id }) mu = false := by
        by_contra hpl
        have hpl' : placedIn (w.cards.set i { id := d.id }) mu = true := by simpa using hpl
        unfold placedIn at hpl'
        rw [List.any_eq_true] at hpl'
        obtain ⟨e, he, hhas⟩ := hpl'
        rcases List.mem_or_eq_of_mem_set he with h2 | h2
        · have : w.placed mu = true := by
            unfold World.placed
            rw [List.any_eq_true]
            exact ⟨e, h2, hhas⟩
          rw [hx0] at this
          cases this
        · rw [h2] at hhas
          simp [Card.has, Card.serving] at hhas
      have := hC rfl hxb1 hx01
      simp only [charged, begins, or_true, and_self, ite_true, decide_true, Bool.or_true, Bool.true_or]
      omega
    · by_cases h0 : w.held t = 0
      · have hot : some t ≠ d.owner := by
          intro h2
          have := heldIn_pos hdmem (by simp [Card.taken, hs]) h2.symm
          rw [← held_eq] at this
          omega
        obtain ⟨hfirst, hrank⟩ := winner_first hwin hw.tenant hlost hot h0
        have hub : u ∈ before w.lines.tenants t := by
          rcases hfirst with h2 | h2
          · exact absurd h2 hut
          · exact h2
        -- rank 0: `u` is not the owner, and holds no card
        have huo : some u ≠ d.owner := by
          intro h2
          simp only [World.rank, h2, ite_true] at hrank
          omega
        have hu0 : w.held u = 0 := by
          simp only [World.rank, huo, ite_false] at hrank
          omega
        have h01 : heldIn (w.cards.set i { id := d.id }) t = 0 := by
          have := hheld1 t
          rw [← held_eq] at this
          omega
        have hu01 : heldIn (w.cards.set i { id := d.id }) u = 0 := by
          have := hheld1 u
          rw [← held_eq] at this
          omega
        have hub1 : u ∈ before (w.lines.ended d.owner d.model).tenants t := by
          cases hown : d.owner with
          | none => simpa using hub
          | some v =>
            have hvt : v ≠ t := fun h2 => hot (by rw [hown, h2])
            have huv : u ≠ v := fun h2 => huo (by rw [hown, h2])
            simp only [ended_tenants, tenantToBack_tenants]
            rw [before_toBack hw.nodup.1 hw.tenant hvt, List.mem_filter]
            exact ⟨hub, by simpa using huv⟩
        have := hB hut h01 hub1 hu01
        simp only [charged, begins, h0, true_or, and_self, ite_true, decide_true, Bool.or_true, Bool.true_or]
        omega
      · have := hA hut
        have hne' : ¬ (some u = some t) := fun h2 => hut (Option.some.inj h2)
        simp only [charged, h0, hne', or_self, and_false, ite_false, Nat.add_zero]
        omega

/-- The charged turns of a round. -/
def mcount : World T M C → Nat → Nat
  | _, 0 => 0
  | w, n + 1 =>
    match w.rule with
    | none => 0
    | some (a, w') => charged t w a + mcount w' n

/-- A whole round of rules, on any number of cards. -/
theorem run_multi : ∀ (fuel : Nat) {w : World T M C}, MWaiting N t m w.cards w.lines →
    (∀ a ∈ (w.run fuel).1, Spares m a) →
    MWaiting N t m (w.run fuel).2.cards (w.run fuel).2.lines ∧
      mPot N t m (w.run fuel).2.cards (w.run fuel).2.lines + mcount t w fuel ≤ mPot N t m w.cards w.lines := by
  intro fuel
  induction fuel with
  | zero => intro w hw _; exact ⟨hw, by simp [World.run, mcount]⟩
  | succ n ih =>
    intro w hw hno
    cases hr : w.rule with
    | none =>
      rw [run_none n hr]
      exact ⟨hw, by simp [mcount, hr]⟩
    | some p =>
      obtain ⟨a, w'⟩ := p
      rw [run_some n hr] at hno ⊢
      obtain ⟨hw1, h1⟩ := rule_multi N t m hw hr (hno a (List.mem_cons_self ..))
      obtain ⟨hw2, h2⟩ := ih hw1 fun b hb => hno b (List.mem_cons_of_mem _ hb)
      refine ⟨hw2, ?_⟩
      simp only [mcount, hr]
      omega

/-- The cards and the lines: what there is between rounds. -/
structure MSys (T M C : Type) where
  cards : List (Card T M C)
  lines : Lines T M

/-- What the world may do between rounds, to one card. -/
inductive MEnv : MSys T M C → MSys T M C → Prop
  /-- requests come and go -/
  | busy (s : MSys T M C) (i : Nat) (c : Card T M C) (inflight busyAt : Nat) : s.cards[i]? = some c →
      MEnv s { s with cards := s.cards.set i { c with inflight := inflight, busyAt := busyAt } }
  /-- a load finishes -/
  | loaded (s : MSys T M C) (i : Nat) (c : Card T M C) (now load : Nat) : s.cards[i]? = some c →
      c.st = .starting →
      MEnv s { s with cards := s.cards.set i { c with st := .up, turnAt := now, busyAt := now, load := load } }
  /-- a load fails, or a server dies at work: the turn is over -/
  | failed (s : MSys T M C) (i : Nat) (c : Card T M C) : s.cards[i]? = some c → c.serving = true →
      MEnv s { cards := s.cards.set i { id := c.id }, lines := s.lines.ended c.owner c.model }
  /-- a server dies while it drains: the card has drained, and is still
  whose it was to be -/
  | died (s : MSys T M C) (i : Nat) (c : Card T M C) : s.cards[i]? = some c → c.st = .draining →
      MEnv s { s with cards := s.cards.set i { id := c.id, owner := c.owner, next := c.next } }

/-- The world `decide` runs in. -/
def MSys.world (s : MSys T M C) (flows : List (Flow T M)) (slots : M → Nat) (now : Nat) (pol : Policy) :
    World T M C :=
  { cards := s.cards, flows, slots, lines := s.lines.join flows, now, pol }

/-- One round: `decide`'s actions, the cards as they leave them, and the lines. -/
def MSys.round (s : MSys T M C) (flows : List (Flow T M)) (slots : M → Nat) (now : Nat) (pol : Policy) :
    List (Action T M C) × MSys T M C :=
  let r := (s.world flows slots now pol).run (3 * s.cards.length + 1)
  (r.1, { cards := r.2.cards, lines := r.2.lines })

/-- A round is `decide`. -/
theorem mround_decide (s : MSys T M C) (flows : List (Flow T M)) (slots : M → Nat) (now : Nat) (pol : Policy) :
    decide s.cards flows slots s.lines now pol =
      ((s.round flows slots now pol).1, (s.round flows slots now pol).2.lines) := rfl

/-- The charged turns of a round. -/
def MSys.charged (s : MSys T M C) (flows : List (Flow T M)) (slots : M → Nat) (now : Nat) (pol : Policy) : Nat :=
  mcount t (s.world flows slots now pol) (3 * s.cards.length + 1)

/-- New requests: the flow still waits, and the measure is no higher. -/
theorem mpot_join {cards : List (Card T M C)} {l : Lines T M} {flows : List (Flow T M)}
    (hw : MWaiting N t m cards l) (hq : hasFlow flows t m = true) (hfew : (l.join flows).tenants.length ≤ N) :
    MWaiting N t m cards (l.join flows) ∧ mPot N t m cards (l.join flows) ≤ mPot N t m cards l := by
  have hqt : hasQueued flows t = true := by
    simp only [hasFlow, hasQueued, List.any_eq_true, decide_eq_true_eq] at hq ⊢
    obtain ⟨f, hf, h1, _⟩ := hq
    exact ⟨f, hf, h1⟩
  have hten : t ∈ (l.join flows).tenants := mem_join_tenants.mpr hqt
  refine ⟨⟨join_nodup _ _, hten, mem_join_models.mpr hq, hfew, hw.away⟩, ?_⟩
  have ha : aPart m ((l.join flows).models t) (placedIn cards) ≤ aPart m (l.models t) (placedIn cards) :=
    aPart_le m (by rw [before_join_models (hw.nodup.2 t) hw.tenant hw.model hq]; exact List.filter_sublist)
      fun _ _ h => h
  have hp : pPart N t (l.join flows).tenants (heldIn cards) ≤ pPart N t l.tenants (heldIn cards) :=
    pPart_le N t (by rw [before_join_tenants hw.nodup.1 hw.tenant hqt]; exact List.filter_sublist)
      (fun _ _ h => h) hten hfew fun h => h
  unfold mPot
  exact Nat.add_le_add (Nat.mul_le_mul_right N ha) hp

/-- What the world does between rounds: the flow still waits, and the
measure is no higher. -/
theorem menv_pot {s s' : MSys T M C} (hw : MWaiting N t m s.cards s.lines) (he : MEnv s s') :
    MWaiting N t m s'.cards s'.lines ∧ mPot N t m s'.cards s'.lines ≤ mPot N t m s.cards s.lines := by
  cases he with
  | busy i c inflight busyAt hi =>
    obtain ⟨hw', he⟩ := mpot_congr N t m { c with inflight := inflight, busyAt := busyAt } hw hi
      (fun _ => rfl) (fun _ => rfl)
    exact ⟨hw', le_of_eq he⟩
  | loaded i c now load hi hst =>
    obtain ⟨hw', he⟩ := mpot_congr N t m { c with st := .up, turnAt := now, busyAt := now, load := load } hw hi
      (by intro v; simp [Card.taken, Card.serving, hst]) (by intro y; simp [Card.has, Card.serving, hst])
    exact ⟨hw', le_of_eq he⟩
  | failed i c hi hs => exact mpot_ended N t m { id := c.id } hw hi hs (by simp [Card.taken, Card.serving])
  | died i c hi hst =>
    obtain ⟨hw', he⟩ := mpot_congr N t m { id := c.id, owner := c.owner, next := c.next } hw hi
      (by intro v; simp [Card.taken, Card.serving, hst]) (by intro y; simp [Card.has, Card.serving, hst])
    exact ⟨hw', le_of_eq he⟩

/-- Any history in which the flow (`t`, `m`) stays queued and `m` is not
started, on any number of cards. The number is the charged turns. -/
inductive MTrace : MSys T M C → Nat → MSys T M C → Prop
  | nil (s : MSys T M C) : MTrace s 0 s
  | env {s s1 s2 : MSys T M C} {n : Nat} : MTrace s n s1 → MEnv s1 s2 → MTrace s n s2
  | round {s s1 : MSys T M C} {n : Nat} (flows : List (Flow T M)) (slots : M → Nat) (now : Nat) (pol : Policy) :
      MTrace s n s1 → hasFlow flows t m = true → (s1.lines.join flows).tenants.length ≤ N →
      (∀ a ∈ (s1.round flows slots now pol).1, Spares m a) →
      MTrace s (n + s1.charged t flows slots now pol) (s1.round flows slots now pol).2

theorem mtrace_pot {s s' : MSys T M C} {n : Nat} (h : MTrace N t m s n s') (hw : MWaiting N t m s.cards s.lines) :
    MWaiting N t m s'.cards s'.lines ∧ mPot N t m s'.cards s'.lines + n ≤ mPot N t m s.cards s.lines := by
  induction h with
  | nil => exact ⟨hw, by simp⟩
  | env _ he ih =>
    obtain ⟨hw1, h1⟩ := ih
    obtain ⟨hw2, h2⟩ := menv_pot N t m hw1 he
    exact ⟨hw2, by omega⟩
  | round flows slots now pol _ hq hfew hno ih =>
    obtain ⟨hw1, h1⟩ := ih
    obtain ⟨hwj, hj⟩ := mpot_join N t m hw1 hq hfew
    obtain ⟨hw2, h2⟩ := run_multi N t m _ (w := MSys.world _ flows slots now pol) hwj hno
    refine ⟨hw2, ?_⟩
    have h3 := Nat.le_trans h2 hj
    have h4 : mPot N t m (MSys.round _ flows slots now pol).2.cards (MSys.round _ flows slots now pol).2.lines +
        MSys.charged t _ flows slots now pol ≤ mPot N t m _ _ := h3
    omega

/-- The measure is at most `K * N - 1`. -/
theorem mPot_le {cards : List (Card T M C)} {l : Lines T M} {K : Nat} (hw : MWaiting N t m cards l)
    (hK : (l.models t).length ≤ K) : mPot N t m cards l ≤ K * N - 1 := by
  have hN : 1 ≤ N := by
    have := List.length_pos_of_mem hw.tenant
    have := hw.few
    omega
  have ha : aPart m (l.models t) (placedIn cards) ≤ K - 1 := by
    unfold aPart
    have h1 := List.length_filter_le (fun y => !placedIn cards y) (before (l.models t) m)
    have h2 := before_length_lt hw.model
    omega
  have hp := pPart_le_max N t (heldIn cards) hw.tenant hw.few
  have hK1 : 1 ≤ K := by
    have := List.length_pos_of_mem hw.model
    omega
  unfold mPot
  have h1 := Nat.mul_le_mul_right N ha
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have h3 : (k + 1) * N = k * N + N := by ring
  simp only [Nat.add_sub_cancel] at h1
  omega

/-- **No starvation, on any number of cards, in turns.** While tenant `t`
has requests queued for model `m`, and until `m` is started or a card
drains for it, at most `K * N - 1` turns begin that are `t`'s own or begin
while `t` holds no card. -/
theorem mturns_bound {s s' : MSys T M C} {n K : Nat} (h : MTrace N t m s n s')
    (hw : MWaiting N t m s.cards s.lines) (hK : (s.lines.models t).length ≤ K) : n ≤ K * N - 1 := by
  have h1 := (mtrace_pot N t m h hw).2
  have h2 := mPot_le N t m hw hK
  omega

/-- **Nobody is overtaken twice round.** For the flow that is first in its
tenant's line: at most `N - 1` charged turns begin before its own -- fewer
than one for each tenant with queued requests. While the tenant holds no
card, every turn that begins goes to somebody who stood before it in the
line and held none either, and nobody is that twice. -/
theorem tenant_turns_bound {s s' : MSys T M C} {n : Nat} (h : MTrace N t m s n s')
    (hw : MWaiting N t m s.cards s.lines) (hhead : before (s.lines.models t) m = []) : n ≤ N - 1 := by
  have h1 := (mtrace_pot N t m h hw).2
  have ha : aPart m (s.lines.models t) (placedIn s.cards) = 0 := by simp [aPart, hhead]
  have hp := pPart_le_max N t (heldIn s.cards) hw.tenant hw.few
  unfold mPot at h1
  rw [ha] at h1
  simp only [Nat.zero_mul, Nat.zero_add] at h1
  omega

end multi

assert_no_sorry tenant_turns_bound
assert_no_sorry mpot_ended

assert_no_sorry mpot_start
assert_no_sorry mpot_pass
assert_no_sorry rule_multi
assert_no_sorry mturns_bound

end Timeshare
