/-
The scheduler does not sit on a decision (one card). While a flow waits:
a free card is started on, a card that has drained is stopped, and a turn
that is a quantum old passes or drains. So the turns `turns_bound` counts
do come to an end: nothing but the model servers' own time (a load, the
requests in flight) and the quantum stands between one turn and the next.
-/
import Timeshare.Proofs.Bound

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

omit [DecidableEq T] [DecidableEq M] in
theorem indexed_single (c : Card T M C) : ([c].zipIdx.map fun p => (p.2, p.1)) = [(0, c)] := rfl

/-- A card that has drained is stopped. -/
theorem progress_drained {w : World T M C} {c : Card T M C} (hc : w.cards = [c]) (hst : c.st = .draining)
    (h0 : c.inflight = 0) : w.rule ≠ none := by
  intro h
  unfold World.rule at h
  simp only [hc, indexed_single] at h
  split at h
  · cases h
  · rename_i hf
    simp [hst, h0] at hf

/-- A free card is started on, while the flow waits. -/
theorem progress_free (N : Nat) (t : T) (m : M) {w : World T M C} {c : Card T M C} (hc : w.cards = [c])
    (hst : c.st = .down) (hw : Waiting N t m c w.lines) : w.rule ≠ none := by
  intro h
  obtain ⟨o, ts, hts⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hw.tenant)
  obtain ⟨x, ms, hms⟩ := List.exists_cons_of_ne_nil (hw.full o (by rw [hts]; exact List.mem_cons_self ..))
  have hfree : ∀ e ∈ w.cards, e.serving = false := by
    intro e he
    rw [hc] at he
    simp only [List.mem_singleton] at he
    rw [he]; simp [Card.serving, hst]
  have hcl := claim_free hfree hts hms
  unfold World.rule at h
  simp only [hc, indexed_single] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hno
      exact hno o x 0 c hcl (by simp [hst])
/-- A turn that is a quantum old passes or drains, while the flow waits:
the flow's tenant has a claim to the card, so somebody wins it, and the
winner is not the owner staying. -/
theorem progress_old (N : Nat) (t : T) (m : M) {w : World T M C} {c : Card T M C} (hc : w.cards = [c])
    (hst : c.st = .up) (hq : w.pol.quantum c ≤ w.now - c.turnAt) (hnew : c.turnAt < w.now)
    (hw : Waiting N t m c w.lines) : w.rule ≠ none := by
  intro h
  have hs : c.serving = true := by simp [Card.serving, hst]
  have hplaced : w.placed m = false := by
    unfold World.placed
    rw [hc]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; exact hw.away hs
  have hlost : (w.lost t).isSome = true := by
    unfold World.lost
    rw [List.find?_isSome]
    exact ⟨m, hw.model, by simp [hplaced]⟩
  obtain ⟨⟨u, mu⟩, hwin⟩ := Option.isSome_iff_exists.mp (winner_isSome hst hq hnew hw.tenant hlost)
  -- the winner is not the owner staying where it is
  have hnot : ¬ (some u = c.owner ∧ some mu = c.model) := by
    rintro ⟨hu, hmu⟩
    by_cases hot : c.owner = some t
    · -- the owner is `t`, who would move
      have hut : u = t := Option.some.inj (hu.trans hot)
      subst hut
      obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hlost
      have hmm := winner_lost hwin hm'
      subst hmm
      have h1 := lost_not_placed hm'
      have h2 : w.placed mu = true := by
        unfold World.placed
        rw [hc]
        simp [hs, hmu.symm]
      rw [h1] at h2
      cases h2
    · -- the owner is somebody else, and comes after `t`, who has no card
      have hheld : w.held t = 0 := by
        unfold World.held
        rw [hc, List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro e he
        simp only [List.mem_singleton] at he
        subst he
        simp [hot]
      have hr := (winner_first hwin hw.tenant hlost (fun h => hot h.symm) hheld).2
      simp [World.rank, hu] at hr
  unfold World.rule at h
  simp only [hc, indexed_single] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · rename_i hdr
            simp [hst] at hdr
          · split at h
            · cases h
            · rename_i hpass
              split at h
              · cases h
              · rename_i hdrain
                by_cases hmu : some mu = c.model
                · -- [Pass] applies
                  have hu : some u ≠ c.owner := fun hu => hnot ⟨hu, hmu⟩
                  simp [hwin, hu, hmu] at hpass
                · -- [Drain] applies
                  exact hdrain 0 c (by simp [hwin, hmu, firstBest]) (by simp [hst])

assert_no_sorry progress_drained
assert_no_sorry progress_free
assert_no_sorry progress_old

end Timeshare
