/-
What one rule does: `rule_effect`. Every rule changes exactly one card, in
one of six ways, each with its reason, its action and its effect on the
lines (`RuleEffect`). The safety claims about a round -- no card that is
answering is stopped, no turn is taken before its quantum -- are read off
that.
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Util.AssertNoSorry
import Timeshare.Policy

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

/-- The cards with their positions, as `rule` looks at them. -/
theorem mem_indexed {α : Type} {l : List α} {i : Nat} {x : α} :
    (i, x) ∈ l.zipIdx.map (fun p => (p.2, p.1)) ↔ l[i]? = some x := by
  simp [List.mem_map, List.mem_zipIdx_iff_getElem?]

theorem firstBest_mem {α : Type} {better : α → α → Bool} :
    ∀ {l : List (Nat × α)} {x}, firstBest l better = some x → x ∈ l := by
  intro l
  unfold firstBest
  suffices h : ∀ (l : List (Nat × α)) (init : Option (Nat × α)) (x),
      l.foldl (fun best x =>
        match best with
        | none => some x
        | some b => if better x.2 b.2 then some x else some b) init = some x →
      x ∈ l ∨ init = some x by
    intro x hx
    rcases h l none x hx with h | h
    · exact h
    · cases h
  intro l
  induction l with
  | nil => intro init x hx; right; simpa using hx
  | cons y ys ih =>
    intro init x hx
    simp only [List.foldl_cons] at hx
    rcases ih _ _ hx with h | h
    · left; exact List.mem_cons_of_mem _ h
    · cases init with
      | none => simp at h; left; simp [h]
      | some b =>
        simp only at h
        split at h
        · simp at h; left; simp [h]
        · right; exact h

omit [DecidableEq T] in
theorem longestIdle_spec {w : World T M C} {d i c} (h : w.longestIdle d = some (i, c)) :
    w.cards[i]? = some c ∧ w.idleFor d c = true := by
  unfold World.longestIdle at h
  have := firstBest_mem h
  rw [List.mem_filter] at this
  exact ⟨mem_indexed.mp this.1, this.2⟩

/-- The six things a rule can do, each with its reason. -/
inductive RuleEffect (w : World T M C) : Action T M C → World T M C → Prop
  /-- [Drained]: the card stops, and stays its next tenant's -/
  | drained (i : Nat) (c : Card T M C) : w.cards[i]? = some c → c.st = .draining → c.inflight = 0 →
      RuleEffect w { kind := .stop, card := c.id, model := c.model }
        { w with cards := w.cards.set i { id := c.id, owner := c.owner, next := c.next } }
  /-- [Start], of a card that drained for somebody -/
  | reserved (i : Nat) (c : Card T M C) : w.cards[i]? = some c → c.st = .down → c.next.isSome = true →
      RuleEffect w { kind := .start, card := c.id, model := c.next, tenant := c.owner }
        { w with cards := w.cards.set i { id := c.id, st := .starting, model := c.next, owner := c.owner, since := w.now } }
  /-- [Start], of a free card -/
  | start (i : Nat) (c : Card T M C) (t : T) (m : M) : w.cards[i]? = some c → c.st = .down →
      c.next = none → w.claim = some (t, m) →
      (∀ d ∈ w.cards, ¬ (d.st = .down ∧ d.next.isSome = true)) →
      RuleEffect w { kind := .start, card := c.id, model := some m, tenant := some t }
        { w with cards := w.cards.set i { id := c.id, st := .starting, model := some m, owner := some t, since := w.now } }
  /-- [GiveWay], [IdleStop] -/
  | stop (i : Nat) (c : Card T M C) (d : Nat) : w.cards[i]? = some c → w.idleFor d c = true →
      RuleEffect w { kind := .stop, card := c.id, model := c.model }
        { w with cards := w.cards.set i { id := c.id }, lines := w.lines.ended c.owner c.model }
  /-- [Pass] -/
  | pass (i : Nat) (c : Card T M C) (t : T) (m : M) : w.cards[i]? = some c → w.winner c = some (t, m) →
      some t ≠ c.owner → some m = c.model →
      RuleEffect w { kind := .pass, card := c.id, model := some m, tenant := some t }
        { w with cards := w.cards.set i { c with owner := some t, turnAt := w.now }
                 lines := w.lines.tenantToBack c.owner }
  /-- [Drain]: the old turn is over, and the card is the winner's, for its model -/
  | drain (i : Nat) (c : Card T M C) (t : T) (m : M) : w.cards[i]? = some c → w.winner c = some (t, m) →
      some m ≠ c.model →
      RuleEffect w { kind := .drain, card := c.id, model := c.model, tenant := some t, next := some m }
        { w with cards := w.cards.set i { c with st := .draining, owner := some t, next := some m, since := w.now }
                 lines := w.lines.ended c.owner c.model }

theorem rule_effect {w w' : World T M C} {a} (h : w.rule = some (a, w')) : RuleEffect w a w' := by
  unfold World.rule at h
  simp only at h
  split at h
  · -- [Drained]
    rename_i i c hf
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    cases h
    exact .drained i c (mem_indexed.mp hm) hp.1 hp.2
  · split at h
    · -- [Start], reserved
      rename_i i c hf
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      cases h
      exact .reserved i c (mem_indexed.mp hm) hp.1 hp.2
    · rename_i hres
      have hnone : ∀ d ∈ w.cards, ¬ (d.st = .down ∧ d.next.isSome = true) := by
        intro d hd hdn
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
        have := List.find?_eq_none.mp hres (j, d) (mem_indexed.mpr hj)
        simp [hdn.1, hdn.2] at this
      split at h
      · -- [Start], free
        rename_i t m i c hc hf
        have hm := List.mem_of_find?_eq_some hf
        have hp := List.find?_some hf
        simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hp
        cases h
        exact .start i c t m (mem_indexed.mp hm) hp.1 hp.2 hc hnone
      · split at h
        · -- [GiveWay]
          rename_i i c hl
          split at hl
          · obtain ⟨hi, hidle⟩ := longestIdle_spec hl
            cases h
            exact .stop i c 0 hi hidle
          · cases hl
        · split at h
          · -- [IdleStop]
            rename_i i c hl
            split at hl
            · obtain ⟨hi, hidle⟩ := longestIdle_spec hl
              cases h
              exact .stop i c _ hi hidle
            · cases hl
          · split at h
            · -- [Pass]
              rename_i i c t m hf
              obtain ⟨p, hpm, hp⟩ := List.exists_of_findSome?_eq_some hf
              split at hp
              · rename_i t' m' hw
                split at hp
                · rename_i hcond
                  cases hp
                  cases h
                  exact .pass i c t m (mem_indexed.mp hpm) hw hcond.1 hcond.2
                · cases hp
              · cases hp
            · split at h
              · -- [Drain]
                rename_i i c t m hb hfree
                have hm := firstBest_mem hb
                rw [List.mem_filterMap] at hm
                obtain ⟨p, hpm, hp⟩ := hm
                split at hp
                · rename_i t' m' hw
                  split at hp
                  · rename_i hne
                    cases hp
                    cases h
                    exact .drain p.1 p.2 t m (mem_indexed.mp hpm) hw hne
                  · cases hp
                · cases hp
              · cases h

/-- What a rule may do to a card. -/
inductive CardStep (w : World T M C) : Card T M C → Card T M C → Prop
  | drained (c) : c.st = .draining → c.inflight = 0 → CardStep w c { id := c.id, owner := c.owner, next := c.next }
  | reserved (c) : c.st = .down →
      CardStep w c { id := c.id, st := .starting, model := c.next, owner := c.owner, since := w.now }
  | start (c t m) : c.st = .down →
      CardStep w c { id := c.id, st := .starting, model := some m, owner := some t, since := w.now }
  | stop (c d) : w.idleFor d c = true → CardStep w c { id := c.id }
  | pass (c t m) : w.winner c = some (t, m) → CardStep w c { c with owner := some t, turnAt := w.now }
  | drain (c t m) : w.winner c = some (t, m) →
      CardStep w c { c with st := .draining, owner := some t, next := some m, since := w.now }


/-- A rule changes one card, by one `CardStep`. -/
theorem rule_step {w w' : World T M C} {a} (h : w.rule = some (a, w')) :
    ∃ i c c', w.cards[i]? = some c ∧ CardStep w c c' ∧ w'.cards = w.cards.set i c' ∧ w'.now = w.now := by
  cases rule_effect h with
  | drained i c hi hst h0 => exact ⟨i, c, _, hi, .drained c hst h0, rfl, rfl⟩
  | reserved i c hi hst _ => exact ⟨i, c, _, hi, .reserved c hst, rfl, rfl⟩
  | start i c t m hi hst _ _ _ => exact ⟨i, c, _, hi, .start c t m hst, rfl, rfl⟩

  | stop i c d hi hidle => exact ⟨i, c, _, hi, .stop c d hidle, rfl, rfl⟩
  | pass i c t m hi hw _ _ => exact ⟨i, c, _, hi, .pass c t m hw, rfl, rfl⟩
  | drain i c t m hi hw _ => exact ⟨i, c, _, hi, .drain c t m hw, rfl, rfl⟩

/-- The best claim is only asked of a card that is up, whose turn is a
quantum old, and did not begin this instant. -/
theorem winner_old {w : World T M C} {c t m} (h : w.winner c = some (t, m)) :
    c.st = .up ∧ w.pol.quantum c ≤ w.now - c.turnAt ∧ c.turnAt < w.now := by
  unfold World.winner at h
  split at h
  · cases h
  · rename_i hc
    push Not at hc
    exact hc

omit [DecidableEq T] in
theorem idleFor_spec {w : World T M C} {d c} (h : w.idleFor d c = true) : c.st = .up ∧ c.inflight = 0 := by
  unfold World.idleFor at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem rule_length {w w' : World T M C} {a} (h : w.rule = some (a, w')) :
    w'.cards.length = w.cards.length := by
  obtain ⟨i, c, c', _, _, hset, -⟩ := rule_step h
  simp [hset]

/-- **NoKill.** No rule stops a card that is answering: a card that is down
after a rule was down before it, or had nothing in flight. -/
theorem rule_noKill {w w' : World T M C} {a} (h : w.rule = some (a, w')) {i : Nat} {c c' : Card T M C}
    (hc : w.cards[i]? = some c) (hc' : w'.cards[i]? = some c') (hd : c'.st = .down) :
    c.st = .down ∨ c.inflight = 0 := by
  obtain ⟨j, d, d', hj, hs, hset, -⟩ := rule_step h
  rw [hset, List.getElem?_set] at hc'
  split at hc'
  · rename_i hij
    subst hij
    rw [hj] at hc
    cases hc
    split at hc'
    · cases hc'
      cases hs with
      | drained _ h0 => right; exact h0
      | reserved _ => cases hd
      | start _ _ hdown => left; exact hdown
      | stop _ hidle => right; exact (idleFor_spec hidle).2
      | pass _ _ _ => left; exact hd
      | drain _ _ _ => cases hd
    · cases hc'
  · rw [hc] at hc'
    cases hc'
    left; exact hd

/-- **No turn is cut short.** A card that is up before a rule and not after
it was idle, or its turn was a quantum old. -/
theorem rule_thrift {w w' : World T M C} {a} (h : w.rule = some (a, w')) {i : Nat} {c c' : Card T M C}
    (hc : w.cards[i]? = some c) (hc' : w'.cards[i]? = some c') (hup : c.st = .up) (hnot : c'.st ≠ .up) :
    (∃ d, w.idleFor d c = true) ∨ w.pol.quantum c ≤ w.now - c.turnAt := by
  obtain ⟨j, d, d', hj, hs, hset, -⟩ := rule_step h
  rw [hset, List.getElem?_set] at hc'
  split at hc'
  · rename_i hij
    subst hij
    rw [hj] at hc
    cases hc
    split at hc'
    · cases hc'
      cases hs with
      | drained hdr _ => rw [hup] at hdr; cases hdr
      | reserved hdown => rw [hup] at hdown; cases hdown
      | start _ _ hdown => rw [hup] at hdown; cases hdown
      | stop d hidle => left; exact ⟨d, hidle⟩
      | pass _ _ _ => exact absurd hup hnot
      | drain _ _ hw => right; exact (winner_old hw).2.1
    · cases hc'
  · rw [hc] at hc'
    cases hc'
    exact absurd hup hnot

/-- A turn changes hands without a swap ([Pass]) only when it is a quantum
old: a card that is up after a rule with another owner than before. -/
theorem rule_pass_old {w w' : World T M C} {a} (h : w.rule = some (a, w')) {i : Nat} {c c' : Card T M C}
    (hc : w.cards[i]? = some c) (hc' : w'.cards[i]? = some c') (hup' : c'.st = .up)
    (hown : c'.owner ≠ c.owner) : w.pol.quantum c ≤ w.now - c.turnAt := by
  obtain ⟨j, d, d', hj, hs, hset, -⟩ := rule_step h
  rw [hset, List.getElem?_set] at hc'
  split at hc'
  · rename_i hij
    subst hij
    rw [hj] at hc
    cases hc
    split at hc'
    · cases hc'
      cases hs with
      | drained _ _ => cases hup'
      | reserved _ => cases hup'
      | start _ _ _ => cases hup'
      | stop _ _ => cases hup'
      | pass _ _ hw => exact (winner_old hw).2.1
      | drain _ _ _ => cases hup'
    · cases hc'
  · rw [hc] at hc'
    cases hc'
    exact absurd rfl hown

assert_no_sorry rule_effect
assert_no_sorry rule_step
assert_no_sorry rule_noKill
assert_no_sorry rule_thrift
assert_no_sorry rule_pass_old

end Timeshare
