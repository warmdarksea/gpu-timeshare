/-
No starvation, on any number of cards, in time: `mwait_bound`. A flow with
queued requests waits at most `K * N * (D + L + Q)` ticks for its model to
be started (or for a card to begin draining for it) -- `L` the longest
load, `D` the longest any requests in flight take, `Q` the longest quantum
(and at least one tick, so a quantum of zero is covered), `N` the most
tenants with queued requests at a time, `K` the number of the flow's
tenant's models with queued requests when the wait begins.

Time is in ticks, and the scheduler has had its say before each one: time
moves only from a state in which a round would decide nothing (`tick`), as
in spec/Turns.tla. Everything else happens at an instant: rounds, and what
the model servers do. A load that has taken `L` must finish or fail before
the next tick, and requests in flight on a draining card end within `D`.

The proof is a budget that no step exceeds (`Bud`): the time now, plus the
measure of MultiBound.lean (`mPot`) times the longest turn, plus the time
left (`rem`) -- while the flow's tenant holds a card, on each of its
cards; while it holds none, on some card. A tick lowers the time left by
one: there is always some left, because when the scheduler would decide
nothing, no turn that matters is old (`settled`, `winner_first`,
`winner_lost`). A turn that begins while the tenant holds no card, or is
its own, lowers the measure (`rule_multi`); so does the turn that takes
its last card (`rule_last`).
-/
import Timeshare.Proofs.NoWaste

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

theorem mul_step {a b k : Nat} (h : a + 1 ≤ b) : a * k + k ≤ b * k := by
  have := Nat.mul_le_mul_right k h
  rw [Nat.add_mul, Nat.one_mul] at this
  exact this

theorem mem_set_self {α : Type} {l : List α} {i : Nat} {c : α} (c' : α) (hi : l[i]? = some c) :
    c' ∈ l.set i c' := by
  have hlt : i < l.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hi
    cases hi
  exact List.mem_iff_getElem?.mpr ⟨i, by simp [hlt]⟩

section timed
variable (N : Nat) (t : T) (m : M) (pol : Policy) (L D : Nat)

/-- The longest quantum, for loads of at most `L`; and at least one tick:
a turn that began this instant can't be taken. -/
def qmax : Nat := max (max pol.maxTimeslice (pol.loadRatio * L)) 1

/-- The longest turn: the drain before it, a load, a quantum. -/
def turn1 : Nat := D + L + qmax pol L

omit [DecidableEq T] [DecidableEq M] in
theorem quantum_le {c : Card T M C} (h : c.load ≤ L) : pol.quantum c ≤ qmax pol L := by
  unfold Policy.quantum qmax
  have := Nat.mul_le_mul_left pol.loadRatio h
  omega

/-- The time left before the turn on the card can be taken: what is left of
the drain before it and of its load, and of its quantum. -/
def rem (now : Nat) (c : Card T M C) : Nat :=
  match c.st with
  | .down => if c.next.isSome = true then L + qmax pol L else 0
  | .starting => (L - (now - c.since)) + qmax pol L
  | .up => qmax pol L - (now - c.turnAt)
  | .draining => (D - (now - c.since)) + L + qmax pol L

omit [DecidableEq T] [DecidableEq M] in
theorem rem_le (now : Nat) (c : Card T M C) : rem pol L D now c ≤ turn1 pol L D := by
  unfold rem turn1
  split
  · split <;> omega
  · omega
  · omega
  · omega

/-- The budget: `C0` is never exceeded by the time now, plus the measure
times the longest turn, plus the time left -- on each of `t`'s cards while
it holds one, on some card while it holds none. -/
def Bud (C0 : Nat) (cards : List (Card T M C)) (l : Lines T M) (now : Nat) : Prop :=
  (heldIn cards t ≠ 0 → ∀ c ∈ cards, (c.taken && Decidable.decide (c.owner = some t)) = true →
    now + mPot N t m cards l * turn1 pol L D + rem pol L D now c ≤ C0) ∧
  (heldIn cards t = 0 → ∃ c ∈ cards, now + mPot N t m cards l * turn1 pol L D + rem pol L D now c ≤ C0)

omit [DecidableEq M] in
theorem heldIn_ne_zero {cards : List (Card T M C)} (h : heldIn cards t ≠ 0) :
    ∃ c ∈ cards, (c.taken && Decidable.decide (c.owner = some t)) = true := by
  unfold heldIn at h
  have hpos : 0 < (cards.filter fun c => c.taken && Decidable.decide (c.owner = some t)).length := by omega
  obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter] at hc
  exact ⟨c, hc.1, hc.2⟩

/-- Either way, the time now and the measure are within the budget. -/
theorem bud_base {C0 : Nat} {cards : List (Card T M C)} {l : Lines T M} {now : Nat}
    (h : Bud N t m pol L D C0 cards l now) : now + mPot N t m cards l * turn1 pol L D ≤ C0 := by
  by_cases h0 : heldIn cards t = 0
  · obtain ⟨c, _, hc⟩ := h.2 h0
    omega
  · obtain ⟨c, hc, hp⟩ := heldIn_ne_zero t h0
    have := h.1 h0 c hc hp
    omega

/-- The measure fell by one: whatever the cards are now, they are within
the budget. -/
theorem bud_begun {C0 Ψ : Nat} {cards' : List (Card T M C)} {l' : Lines T M} {now : Nat}
    (hbase : now + Ψ * turn1 pol L D ≤ C0) (hlt : mPot N t m cards' l' + 1 ≤ Ψ) (hne : cards' ≠ []) :
    Bud N t m pol L D C0 cards' l' now := by
  have hstep := mul_step (k := turn1 pol L D) hlt
  have hall : ∀ c : Card T M C, now + mPot N t m cards' l' * turn1 pol L D + rem pol L D now c ≤ C0 := by
    intro c
    have := rem_le pol L D now c
    omega
  refine ⟨fun _ c _ _ => hall c, fun _ => ?_⟩
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact ⟨c, List.mem_cons_self .., hall c⟩

/-- A card changes but is as much `t`'s as before, with no more time left,
and the measure is no higher: still within the budget. -/
theorem bud_quiet {C0 : Nat} {cards : List (Card T M C)} {l l' : Lines T M} {now i : Nat} {c : Card T M C}
    (c' : Card T M C) (h : Bud N t m pol L D C0 cards l now) (hi : cards[i]? = some c)
    (hpot : mPot N t m (cards.set i c') l' ≤ mPot N t m cards l)
    (hrem : rem pol L D now c' ≤ rem pol L D now c)
    (hwho : (c'.taken && Decidable.decide (c'.owner = some t)) = (c.taken && Decidable.decide (c.owner = some t))) :
    Bud N t m pol L D C0 (cards.set i c') l' now := by
  have hheld : heldIn (cards.set i c') t = heldIn cards t := by
    have := heldIn_set c' t hi
    rw [hwho] at this
    omega
  have hmul := Nat.mul_le_mul_right (turn1 pol L D) hpot
  have hcmem : c ∈ cards := List.mem_of_getElem? hi
  refine ⟨fun h0 e he hp => ?_, fun h0 => ?_⟩
  · rw [hheld] at h0
    rcases List.mem_or_eq_of_mem_set he with h1 | h1
    · have := h.1 h0 e h1 hp
      omega
    · subst h1
      rw [hwho] at hp
      have := h.1 h0 c hcmem hp
      omega
  · rw [hheld] at h0
    obtain ⟨e, he, hb⟩ := h.2 h0
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    by_cases hji : j = i
    · subst hji
      rw [hi] at hj
      cases hj
      exact ⟨c', mem_set_self c' hi, by omega⟩
    · refine ⟨e, List.mem_iff_getElem?.mpr ⟨j, ?_⟩, by omega⟩
      rw [List.getElem?_set_ne (Ne.symm hji)]
      exact hj

/-- A card becomes nobody's, with no time left, and the measure is no
higher: still within the budget. -/
theorem bud_freed {C0 : Nat} {cards : List (Card T M C)} {l l' : Lines T M} {now i : Nat} {c : Card T M C}
    (c' : Card T M C) (h : Bud N t m pol L D C0 cards l now) (hi : cards[i]? = some c)
    (hpot : mPot N t m (cards.set i c') l' ≤ mPot N t m cards l)
    (hrem : rem pol L D now c' = 0) (hfree : c'.taken = false) :
    Bud N t m pol L D C0 (cards.set i c') l' now := by
  have hbase := bud_base N t m pol L D h
  have hmul := Nat.mul_le_mul_right (turn1 pol L D) hpot
  have hheld : heldIn (cards.set i c') t ≤ heldIn cards t := by
    have := heldIn_set c' t hi
    simp only [hfree, Bool.false_and, Bool.false_eq_true, ite_false] at this
    omega
  refine ⟨fun h0 e he hp => ?_, fun _ => ⟨c', mem_set_self c' hi, by omega⟩⟩
  have h0' : heldIn cards t ≠ 0 := by omega
  rcases List.mem_or_eq_of_mem_set he with h1 | h1
  · have := h.1 h0' e h1 hp
    omega
  · subst h1
    rw [hfree] at hp
    simp at hp

/-- A card becomes somebody else's while `t` holds a card before and after,
and the measure is no higher: still within the budget. -/
theorem bud_other {C0 : Nat} {cards : List (Card T M C)} {l l' : Lines T M} {now i : Nat} {c : Card T M C}
    (c' : Card T M C) (h : Bud N t m pol L D C0 cards l now) (hi : cards[i]? = some c)
    (hpot : mPot N t m (cards.set i c') l' ≤ mPot N t m cards l)
    (h0 : heldIn cards t ≠ 0) (h0' : heldIn (cards.set i c') t ≠ 0)
    (hnot : (c'.taken && Decidable.decide (c'.owner = some t)) = false) :
    Bud N t m pol L D C0 (cards.set i c') l' now := by
  have hmul := Nat.mul_le_mul_right (turn1 pol L D) hpot
  refine ⟨fun _ e he hp => ?_, fun hz => absurd hz h0'⟩
  rcases List.mem_or_eq_of_mem_set he with h1 | h1
  · have := h.1 h0 e h1 hp
    omega
  · subst h1
    rw [hnot] at hp
    cases hp

end timed

end Timeshare
