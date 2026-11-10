/-
What one rule does to the cards: `rule_step`. Every rule changes exactly
one card, in one of six ways (`CardStep`). The safety claims about a
round -- no card that is answering is stopped, no turn is taken before its
quantum -- are read off that.
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

/-- What a rule may do to a card. -/
inductive CardStep (w : World T M C) : Card T M C → Card T M C → Prop
  /-- [Drained] -/
  | drained (c) : c.st = .draining → c.inflight = 0 → CardStep w c { id := c.id }
  /-- [Start] -/
  | start (c t m) : c.st = .down → CardStep w c { id := c.id, st := .starting, model := some m, owner := some t }
  /-- [GiveWay], [IdleStop] -/
  | stop (c d) : w.idleFor d c = true → CardStep w c { id := c.id }
  /-- [Pass] -/
  | pass (c t m) : w.winner c = some (t, m) → CardStep w c { c with owner := some t, turnAt := w.now }
  /-- [Drain] -/
  | drain (c t m) : w.winner c = some (t, m) → CardStep w c { c with st := .draining }

omit [DecidableEq T] in
theorem longestIdle_spec {w : World T M C} {d i c} (h : w.longestIdle d = some (i, c)) :
    w.cards[i]? = some c ∧ w.idleFor d c = true := by
  unfold World.longestIdle at h
  have := firstBest_mem h
  rw [List.mem_filter] at this
  exact ⟨mem_indexed.mp this.1, this.2⟩

/-- A rule changes one card, by one `CardStep`. -/
theorem rule_step {w w' : World T M C} {a} (h : w.rule = some (a, w')) :
    ∃ i c c', w.cards[i]? = some c ∧ CardStep w c c' ∧ w'.cards = w.cards.set i c' ∧ w'.now = w.now := by
  unfold World.rule at h
  simp only at h
  split at h
  · -- [Drained]
    rename_i i c hf
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    cases h
    exact ⟨i, c, _, mem_indexed.mp hm, .drained c hp.1 hp.2, rfl, rfl⟩
  · split at h
    · -- [Start]
      rename_i t m i c hc hf
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [decide_eq_true_eq] at hp
      cases h
      exact ⟨i, c, _, mem_indexed.mp hm, .start c t m hp, rfl, rfl⟩
    · split at h
      · -- [GiveWay]
        rename_i i c hl
        split at hl
        · obtain ⟨hi, hidle⟩ := longestIdle_spec hl
          cases h
          exact ⟨i, c, _, hi, .stop c 0 hidle, rfl, rfl⟩
        · cases hl
      · split at h
        · -- [IdleStop]
          rename_i i c hl
          split at hl
          · obtain ⟨hi, hidle⟩ := longestIdle_spec hl
            cases h
            exact ⟨i, c, _, hi, .stop c _ hidle, rfl, rfl⟩
          · cases hl
        · split at h
          · cases h
          · split at h
            · -- [Pass]
              rename_i i c t m hf
              obtain ⟨p, hpm, hp⟩ := List.exists_of_findSome?_eq_some hf
              split at hp
              · rename_i t' m' hw
                split at hp
                · cases hp
                  cases h
                  exact ⟨i, c, _, mem_indexed.mp hpm, .pass c t m hw, rfl, rfl⟩
                · cases hp
              · cases hp
            · split at h
              · -- [Drain]
                rename_i i c hb hfree
                have hm := firstBest_mem hb
                rw [List.mem_filter] at hm
                obtain ⟨hmem, hwin⟩ := hm
                split at hwin
                · rename_i t m hw
                  cases h
                  exact ⟨i, c, _, mem_indexed.mp hmem, .drain c t m hw, rfl, rfl⟩
                · cases hwin
              · cases h

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
      | start _ _ _ => cases hup'
      | stop _ _ => cases hup'
      | pass _ _ hw => exact (winner_old hw).2.1
      | drain _ _ _ => cases hup'
    · cases hc'
  · rw [hc] at hc'
    cases hc'
    exact absurd rfl hown

assert_no_sorry rule_step
assert_no_sorry rule_noKill
assert_no_sorry rule_thrift
assert_no_sorry rule_pass_old

end Timeshare
