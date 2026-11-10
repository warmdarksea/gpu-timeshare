/-
The last step of a wait: `up_bound`. Once a card has a model coming -- it
drains for it, has drained for it, or is loading it -- the model is up
within `D + L` ticks, unless its load fails: nothing the scheduler does
takes such a card for anything else.

With `mwait_bound` (MultiWait.lean): a flow with queued requests has its
model up within `K * N * (D + L + Q) + D + L` ticks, on any number of
cards, if its load does not fail.
-/
import Timeshare.Proofs.MultiWait

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

section up
variable (m : M) (pol : Policy) (L D : Nat)

/-- The time until a card that has `m` coming has it up, at most. -/
def tup (now : Nat) (c : Card T M C) : Nat :=
  match c.st with
  | .draining => (D - (now - c.since)) + L
  | .down => L
  | .starting => L - (now - c.since)
  | .up => 0

/-- `m` is coming on the card, and not up yet; and its clock is not ahead. -/
def Coming (now : Nat) (c : Card T M C) : Prop :=
  c.st ≠ .up ∧ c.has m = true ∧ ((c.st = .starting ∨ c.st = .draining) → c.since ≤ now)

/-- No rule takes a card that has `m` coming for anything else, or adds to
the time it has left. -/
theorem rule_coming {w w' : World T M C} {a : Action T M C} {i : Nat} {c : Card T M C}
    (hi : w.cards[i]? = some c) (hc : Coming m w.now c) (h : w.rule = some (a, w')) :
    ∃ c', w'.cards[i]? = some c' ∧ Coming m w.now c' ∧ tup L D w.now c' ≤ tup L D w.now c := by
  obtain ⟨hnup, hhas, hsince⟩ := hc
  have hlt : i < w.cards.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hi
    cases hi
  -- a rule on another card leaves this one alone
  have other : ∀ (j : Nat) (c' : Card T M C), j ≠ i → (w.cards.set j c')[i]? = some c := by
    intro j c' hji
    rw [List.getElem?_set_ne hji]
    exact hi
  have same : ∀ {j : Nat} {d : Card T M C}, w.cards[j]? = some d → j = i → d = c := by
    intro j d hd hji
    subst hji
    rw [hi] at hd
    exact (Option.some.inj hd).symm
  cases rule_effect h with
  | drained j d hd hst _ =>
    by_cases hji : j = i
    · have hdc := same hd hji
      subst hdc
      subst hji
      refine ⟨{ id := d.id, owner := d.owner, next := d.next }, by simp [hlt], ⟨by simp, ?_, by simp⟩, ?_⟩
      · simpa [Card.has, Card.serving, hst] using hhas
      · simp only [tup, hst]
        omega
    · exact ⟨c, other j _ hji, ⟨hnup, hhas, hsince⟩, le_rfl⟩
  | reserved j d hd hst hnext =>
    by_cases hji : j = i
    · have hdc := same hd hji
      subst hdc
      subst hji
      refine ⟨{ id := d.id, st := .starting, model := d.next, owner := d.owner, since := w.now },
        by simp [hlt], ⟨by simp, ?_, fun _ => le_rfl⟩, ?_⟩
      · simpa [Card.has, Card.serving, hst] using hhas
      · simp [tup, hst]

    · exact ⟨c, other j _ hji, ⟨hnup, hhas, hsince⟩, le_rfl⟩
  | start j d u x hd hst hnext _ _ =>
    by_cases hji : j = i
    · -- a free card has nothing coming
      have hdc := same hd hji
      subst hdc
      simp [Card.has, Card.serving, hst, hnext] at hhas
    · exact ⟨c, other j _ hji, ⟨hnup, hhas, hsince⟩, le_rfl⟩
  | stop j d dur hd hidle =>
    by_cases hji : j = i
    · have hdc := same hd hji
      subst hdc
      exact absurd (idleFor_spec hidle).1 hnup
    · exact ⟨c, other j _ hji, ⟨hnup, hhas, hsince⟩, le_rfl⟩
  | pass j d u mu hd hwin _ _ =>
    by_cases hji : j = i
    · have hdc := same hd hji
      subst hdc
      exact absurd (winner_old hwin).1 hnup
    · exact ⟨c, other j _ hji, ⟨hnup, hhas, hsince⟩, le_rfl⟩
  | drain j d u mu hd hwin _ =>
    by_cases hji : j = i
    · have hdc := same hd hji
      subst hdc
      exact absurd (winner_old hwin).1 hnup
    · exact ⟨c, other j _ hji, ⟨hnup, hhas, hsince⟩, le_rfl⟩

theorem run_coming : ∀ (fuel : Nat) {w : World T M C} {i : Nat} {c : Card T M C},
    w.cards[i]? = some c → Coming m w.now c →
    ∃ c', (w.run fuel).2.cards[i]? = some c' ∧ Coming m w.now c' ∧ tup L D w.now c' ≤ tup L D w.now c := by
  intro fuel
  induction fuel with
  | zero => intro w i c hi hc; exact ⟨c, hi, hc, le_rfl⟩
  | succ n ih =>
    intro w i c hi hc
    cases hr : w.rule with
    | none =>
      rw [run_none n hr]
      exact ⟨c, hi, hc, le_rfl⟩
    | some p =>
      obtain ⟨a, w'⟩ := p
      rw [run_some n hr]
      obtain ⟨c1, hi1, hc1, h1⟩ := rule_coming m L D hi hc hr
      obtain ⟨_, _, _, _, _, _, hn⟩ := rule_step hr
      rw [← hn] at hc1
      obtain ⟨c2, hi2, hc2, h2⟩ := ih hi1 hc1
      rw [hn] at hc2 h2
      exact ⟨c2, hi2, hc2, le_trans h2 h1⟩

/-- What can happen, with nothing assumed about who waits for what. -/
inductive GStep : TSys T M C → TSys T M C → Prop
  | busy (s : TSys T M C) (j : Nat) (c : Card T M C) (inflight busyAt : Nat) : s.sys.cards[j]? = some c →
      GStep s { s with sys := { s.sys with cards := s.sys.cards.set j { c with inflight := inflight, busyAt := busyAt } } }
  | loaded (s : TSys T M C) (j : Nat) (c : Card T M C) (load : Nat) : s.sys.cards[j]? = some c →
      c.st = .starting →
      GStep s { s with sys := { s.sys with cards := s.sys.cards.set j { c with st := .up, turnAt := s.now, busyAt := s.now, load := load } } }
  | failed (s : TSys T M C) (j : Nat) (c : Card T M C) : s.sys.cards[j]? = some c → c.serving = true →
      GStep s { s with sys := { cards := s.sys.cards.set j { id := c.id }, lines := s.sys.lines.ended c.owner c.model } }
  | died (s : TSys T M C) (j : Nat) (c : Card T M C) : s.sys.cards[j]? = some c → c.st = .draining →
      GStep s { s with sys := { s.sys with cards := s.sys.cards.set j { id := c.id, owner := c.owner, next := c.next } } }
  | round (s : TSys T M C) (flows : List (Flow T M)) (slots : M → Nat) :
      GStep s { sys := (s.sys.round flows slots s.now pol).2, now := s.now }
  | tick (s : TSys T M C) (flows : List (Flow T M)) (slots : M → Nat) :
      (s.sys.world flows slots s.now pol).rule = none →
      (∀ c ∈ s.sys.cards, (c.st = .starting → s.now - c.since < L) ∧
        (c.st = .draining → 0 < c.inflight → s.now - c.since < D)) →
      GStep s { s with now := s.now + 1 }

/-- Any history in which card `i` has `m` coming all along: the load has
not finished, and has not failed. -/
inductive UTrace (i : Nat) : TSys T M C → TSys T M C → Prop
  | nil (s : TSys T M C) : UTrace i s s
  | step {s s1 s2 : TSys T M C} : UTrace i s s1 → GStep pol L D s1 s2 →
      (∃ c, s2.sys.cards[i]? = some c ∧ c.st ≠ .up ∧ c.has m = true) → UTrace i s s2

omit [DecidableEq T] [DecidableEq M] in
theorem tup_le (now : Nat) (c : Card T M C) : tup L D now c ≤ D + L := by
  unfold tup
  split <;> omega

theorem eq_of_set_self {α : Type} {l : List α} {i : Nat} {c c' e : α} (hi : l[i]? = some c)
    (h : (l.set i c')[i]? = some e) : e = c' := by
  have hlt : i < l.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hi
    cases hi
  simpa [hlt] using h.symm

theorem eq_of_set_ne {α : Type} {l : List α} {i j : Nat} {c c' e : α} (hji : j ≠ i) (hi : l[i]? = some c)
    (h : (l.set j c')[i]? = some e) : e = c := by
  rw [List.getElem?_set_ne hji, hi] at h
  exact (Option.some.inj h).symm

omit [DecidableEq T] [DecidableEq M] in
/-- A tick takes one from the time a coming model has left, if no load or
drain is overdue. -/
theorem tup_tick (now : Nat) (c : Card T M C) (hnup : c.st ≠ .up) (hdown : c.st ≠ .down)
    (hs : c.st = .starting → now - c.since < L ∧ c.since ≤ now)
    (hd : c.st = .draining → now - c.since < D ∧ c.since ≤ now) :
    tup L D (now + 1) c + 1 ≤ tup L D now c := by
  cases hst : c.st with
  | up => exact absurd hst hnup
  | down => exact absurd hst hdown
  | starting =>
    have := hs hst
    simp only [tup, hst]
    omega
  | draining =>
    have := hd hst
    simp only [tup, hst]
    omega

/-- **A model that is coming is up within `D + L`**, unless its load fails. -/
theorem up_bound {i : Nat} {s s' : TSys T M C} {c0 : Card T M C} (h : UTrace m pol L D i s s')
    (hi : s.sys.cards[i]? = some c0) (hc : Coming m s.now c0) : s'.now ≤ s.now + D + L := by
  suffices hinv : ∃ c, s'.sys.cards[i]? = some c ∧ Coming m s'.now c ∧ s'.now + tup L D s'.now c ≤ s.now + D + L by
    obtain ⟨c, _, _, hb⟩ := hinv
    omega
  induction h with
  | nil =>
    have := tup_le L D s.now c0
    exact ⟨c0, hi, hc, by omega⟩
  | step _ hs hpost ih =>
    obtain ⟨c, hci, hcc, hb⟩ := ih
    obtain ⟨cp, hcp, hpup, hphas⟩ := hpost
    obtain ⟨hnup, hhas, hsince⟩ := hcc
    cases hs with
    | busy j d inflight busyAt hd =>
      by_cases hji : j = i
      · subst hji
        rw [hci] at hd
        cases hd
        have hx := eq_of_set_self hci hcp
        subst hx
        exact ⟨_, hcp, ⟨hnup, hhas, hsince⟩, hb⟩
      · have hx := eq_of_set_ne hji hci hcp
        subst hx
        exact ⟨cp, hcp, ⟨hnup, hhas, hsince⟩, hb⟩
    | loaded j d load hd hst =>
      by_cases hji : j = i
      · subst hji
        have hx := eq_of_set_self hd hcp
        subst hx
        exact absurd rfl hpup
      · have hx := eq_of_set_ne hji hci hcp
        subst hx
        exact ⟨cp, hcp, ⟨hnup, hhas, hsince⟩, hb⟩
    | failed j d hd hs =>
      by_cases hji : j = i
      · subst hji
        have hx := eq_of_set_self hd hcp
        subst hx
        simp [Card.has, Card.serving] at hphas
      · have hx := eq_of_set_ne hji hci hcp
        subst hx
        exact ⟨cp, hcp, ⟨hnup, hhas, hsince⟩, hb⟩
    | died j d hd hst =>
      by_cases hji : j = i
      · subst hji
        rw [hci] at hd
        cases hd
        have hx := eq_of_set_self hci hcp
        subst hx
        refine ⟨_, hcp, ⟨by simp, hphas, by simp⟩, ?_⟩
        simp only [tup, hst] at hb ⊢
        omega
      · have hx := eq_of_set_ne hji hci hcp
        subst hx
        exact ⟨cp, hcp, ⟨hnup, hhas, hsince⟩, hb⟩
    | round flows slots =>
      obtain ⟨c', hc', hcm, hle⟩ := run_coming m L D _ (w := MSys.world _ flows slots _ pol) hci
        ⟨hnup, hhas, hsince⟩
      exact ⟨c', hc', hcm, le_trans (Nat.add_le_add_left hle _) hb⟩
    | tick flows slots hrule hover =>
      obtain ⟨hs1, hs2, _, _, _, _⟩ := settled hrule
      have hmem := List.mem_of_getElem? hci
      obtain ⟨hov1, hov2⟩ := hover c hmem
      have hdown : c.st ≠ .down := by
        intro hst
        -- it has `m` coming, so it has drained for it and waits: but then a rule applies
        have hnext : c.next.isSome = true := by
          simp only [Card.has, Card.serving, hst, reduceCtorEq, decide_false, Bool.or_self,
            Bool.false_eq_true, ite_false, decide_eq_true_eq] at hhas
          simp [hhas]
        exact hs2 c hmem ⟨hst, hnext⟩
      have hstep := tup_tick L D _ c hnup hdown
        (fun hst => ⟨hov1 hst, hsince (Or.inl hst)⟩)
        (fun hst => ⟨hov2 hst (Nat.pos_of_ne_zero (hs1 c hmem hst)), hsince (Or.inr hst)⟩)
      refine ⟨c, hci, ⟨hnup, hhas, fun hx => Nat.le_succ_of_le (hsince hx)⟩, ?_⟩
      show _ + 1 + tup L D (_ + 1) c ≤ _
      omega

end up

assert_no_sorry up_bound

end Timeshare
