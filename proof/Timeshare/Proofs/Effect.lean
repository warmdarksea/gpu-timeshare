/-
Everything a rule does: `rule_effect`. `rule_step` says what happens to
the cards; this adds the action, the lines and why the rule applied.
-/
import Timeshare.Proofs.Lines

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

/-- The five things a rule can do, each with its reason. -/
inductive RuleEffect (w : World T M C) : Action T M C → World T M C → Prop
  /-- [Drained] -/
  | drained (i : Nat) (c : Card T M C) : w.cards[i]? = some c → c.st = .draining → c.inflight = 0 →
      RuleEffect w { kind := .stop, card := c.id, model := c.model }
        { w with cards := w.cards.set i { id := c.id } }
  /-- [Start] -/
  | start (i : Nat) (c : Card T M C) (t : T) (m : M) : w.cards[i]? = some c → c.st = .down →
      w.claim = some (t, m) →
      RuleEffect w { kind := .start, card := c.id, model := some m, tenant := some t }
        { w with cards := w.cards.set i { id := c.id, st := .starting, model := some m, owner := some t } }
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
  /-- [Drain] -/
  | drain (i : Nat) (c : Card T M C) (t : T) (m : M) : w.cards[i]? = some c → w.winner c = some (t, m) →
      some m ≠ c.model →
      RuleEffect w { kind := .drain, card := c.id, model := c.model }
        { w with cards := w.cards.set i { c with st := .draining }, lines := w.lines.ended c.owner c.model }

theorem rule_effect {w w' : World T M C} {a} (h : w.rule = some (a, w')) : RuleEffect w a w' := by
  unfold World.rule at h
  simp only at h
  split at h
  · rename_i i c hf
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    cases h
    exact .drained i c (mem_indexed.mp hm) hp.1 hp.2
  · split at h
    · rename_i t m i c hc hf
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [decide_eq_true_eq] at hp
      cases h
      exact .start i c t m (mem_indexed.mp hm) hp hc
    · split at h
      · rename_i i c hl
        split at hl
        · obtain ⟨hi, hidle⟩ := longestIdle_spec hl
          cases h
          exact .stop i c 0 hi hidle
        · cases hl
      · split at h
        · rename_i i c hl
          split at hl
          · obtain ⟨hi, hidle⟩ := longestIdle_spec hl
            cases h
            exact .stop i c _ hi hidle
          · cases hl
        · split at h
          · cases h
          · split at h
            · rename_i i c t m hf
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
              · rename_i i c hb hfree
                have hm := firstBest_mem hb
                rw [List.mem_filter] at hm
                obtain ⟨hmem, hwin⟩ := hm
                split at hwin
                · rename_i t m hw
                  cases h
                  exact .drain i c t m (mem_indexed.mp hmem) hw (by simpa using hwin)
                · cases hwin
              · cases h

assert_no_sorry rule_effect

end Timeshare
