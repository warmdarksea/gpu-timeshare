/-
No waste, and no decision left pending, on any number of cards:
`settled`. When no rule applies:

- no draining card has finished (it would have been stopped);
- no card is free while a model is lost or short (`claim`);
- no card is free or idle while a model is lost;
- no card has been idle for `idle`;
- and, unless a card is draining, no turn can be taken: wherever a turn is
  old enough to have a winner, the winner is the owner, staying.

So the scheduler never holds a card back, and never waits to do what it
could do now. The one thing it waits for is a drain: one card drains at a
time.
-/
import Timeshare.Proofs.MultiBound

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

theorem firstBest_isSome {α : Type} (better : α → α → Bool) :
    ∀ (l : List (Nat × α)), l ≠ [] → (firstBest l better).isSome = true := by
  have step : ∀ (l : List (Nat × α)) (init : Option (Nat × α)), (init.isSome = true ∨ l ≠ []) →
      (l.foldl (fun best x =>
        match best with
        | none => some x
        | some b => if better x.2 b.2 then some x else some b) init).isSome = true := by
    intro l
    induction l with
    | nil =>
      intro init h
      rcases h with h | h
      · simpa using h
      · exact absurd rfl h
    | cons y ys ih =>
      intro init _
      rw [List.foldl_cons]
      apply ih
      left
      cases init with
      | none => rfl
      | some b => simp only; split <;> rfl
  intro l hl
  exact step l none (Or.inr hl)

omit [DecidableEq T] [DecidableEq M] in
theorem indexed_of_mem {l : List (Card T M C)} {c : Card T M C} (h : c ∈ l) :
    ∃ i, (i, c) ∈ l.zipIdx.map (fun p => (p.2, p.1)) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  exact ⟨i, mem_indexed.mpr hi⟩

omit [DecidableEq T] in
/-- No card has been idle for `d`, if `longestIdle d` finds none. -/
theorem longestIdle_none {w : World T M C} {d : Nat} (h : w.longestIdle d = none) :
    ∀ c ∈ w.cards, w.idleFor d c = false := by
  intro c hc
  obtain ⟨i, hi⟩ := indexed_of_mem hc
  unfold World.longestIdle at h
  by_contra hid
  have hmem : (i, c) ∈ (w.cards.zipIdx.map fun p => (p.2, p.1)).filter fun p => w.idleFor d p.2 :=
    List.mem_filter.mpr ⟨hi, by simpa using hid⟩
  have := firstBest_isSome (fun (c b : Card T M C) => Decidable.decide (c.busyAt < b.busyAt)) _
    (List.ne_nil_of_mem hmem)
  rw [h] at this
  cases this

/-- A tenant with a lost model has a claim to a free card. -/
theorem claim_isSome {w : World T M C} (h : w.anyLost = true) : w.claim.isSome = true := by
  unfold World.anyLost at h
  rw [List.any_eq_true] at h
  obtain ⟨u, hu, hl⟩ := h
  unfold World.claim
  refine firstLowest_isSome hu ?_
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hl
  simp [hx]

/-- Whoever wins a card to put another model there has a claim to a free
card too. -/
theorem claim_of_winner {w : World T M C} {c : Card T M C} {u : T} {mu : M}
    (hwin : w.winner c = some (u, mu)) (hne : some mu ≠ c.model) : w.claim.isSome = true := by
  unfold World.winner at hwin
  split at hwin
  · cases hwin
  · obtain ⟨hu, hpick⟩ := firstLowest_some hwin
    unfold World.claim
    refine firstLowest_isSome hu ?_
    unfold World.pick at hpick
    cases hl : w.lost u with
    | some x => simp
    | none =>
      rw [hl] at hpick
      simp only at hpick
      split at hpick
      · exact absurd hpick.symm hne
      · split at hpick
        · -- a copy: the model is short, whatever is on this card
          unfold World.short at hpick ⊢
          have hmem := List.mem_of_find?_eq_some hpick
          have hp := List.find?_some hpick
          simp only [Option.orElse_none]
          rw [List.find?_isSome]
          refine ⟨mu, hmem, ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
          exact ⟨⟨by simp, hp.1.2⟩, hp.2⟩
        · cases hpick

/-- **No waste, and nothing left undecided.** -/
theorem settled {w : World T M C} (h : w.rule = none) :
    (∀ c ∈ w.cards, c.st = .draining → c.inflight ≠ 0) ∧
    ((∃ c ∈ w.cards, c.st = .down) → w.claim = none) ∧
    (w.anyLost = true → ∀ c ∈ w.cards, c.st ≠ .down ∧ w.idleFor 0 c = false) ∧
    (w.pol.idle > 0 → ∀ c ∈ w.cards, w.idleFor w.pol.idle c = false) ∧
    ((∀ c ∈ w.cards, c.st ≠ .draining) →
      ∀ c ∈ w.cards, ∀ u mu, w.winner c = some (u, mu) → some u = c.owner ∧ some mu = c.model) := by
  unfold World.rule at h
  simp only at h
  split at h
  · cases h
  · rename_i hdrained
    split at h
    · cases h
    · rename_i hstart
      split at h
      · cases h
      · rename_i hgive
        split at h
        · cases h
        · rename_i hidle
          -- the first three need nothing more
          have h1 : ∀ c ∈ w.cards, c.st = .draining → c.inflight ≠ 0 := by
            intro c hc hst h0
            obtain ⟨i, hi⟩ := indexed_of_mem hc
            have := List.find?_eq_none.mp hdrained (i, c) hi
            simp [hst, h0] at this
          have h2 : (∃ c ∈ w.cards, c.st = .down) → w.claim = none := by
            rintro ⟨c, hc, hst⟩
            obtain ⟨i, hi⟩ := indexed_of_mem hc
            have hsome : ((w.cards.zipIdx.map fun p => (p.2, p.1)).find? fun p => p.2.st = .down).isSome = true := by
              rw [List.find?_isSome]
              exact ⟨(i, c), hi, by simp [hst]⟩
            obtain ⟨⟨j, d⟩, hjd⟩ := Option.isSome_iff_exists.mp hsome
            cases hcl : w.claim with
            | none => rfl
            | some p =>
              obtain ⟨u, x⟩ := p
              exact absurd hjd (fun hjd => hstart u x j d hcl hjd)
          have h3 : w.anyLost = true → ∀ c ∈ w.cards, c.st ≠ .down ∧ w.idleFor 0 c = false := by
            intro hl
            have hcl := claim_isSome hl
            have hnodown : ∀ c ∈ w.cards, c.st ≠ .down := by
              intro c hc hst
              rw [h2 ⟨c, hc, hst⟩] at hcl
              cases hcl
            have hfree : ((w.cards.zipIdx.map fun p => (p.2, p.1)).find? fun p => p.2.st = .down) = none := by
              rw [List.find?_eq_none]
              intro p hp
              obtain ⟨i, c⟩ := p
              have hc : c ∈ w.cards := List.mem_of_getElem? (mem_indexed.mp hp)
              simpa using hnodown c hc
            rw [hfree] at hgive
            simp only [Option.isNone_none, hl, Bool.and_self, ite_true] at hgive
            intro c hc
            exact ⟨hnodown c hc, longestIdle_none hgive c hc⟩
          have h4 : w.pol.idle > 0 → ∀ c ∈ w.cards, w.idleFor w.pol.idle c = false := by
            intro hpos
            rw [ite_eq_left hpos] at hidle
            exact longestIdle_none hidle
          refine ⟨h1, h2, h3, h4, ?_⟩
          intro hnodrain c hc u mu hwin
          split at h
          · rename_i hany
            rw [List.any_eq_true] at hany
            obtain ⟨⟨i, d⟩, hd, hst⟩ := hany
            exact absurd (by simpa using hst) (hnodrain d (List.mem_of_getElem? (mem_indexed.mp hd)))
          · split at h
            · cases h
            · rename_i hpass
              split at h
              · cases h
              · rename_i hdrain
                obtain ⟨i, hi⟩ := indexed_of_mem hc
                have hmod : some mu = c.model := by
                  by_contra hne
                  -- the card is wanted, so it would drain -- unless a card is free; but then it would be started on
                  have hwanted : (i, c) ∈ (w.cards.zipIdx.map fun p => (p.2, p.1)).filter fun p =>
                      match w.winner p.2 with
                      | some (_, m) => Decidable.decide (some m ≠ p.2.model)
                      | none => false := by
                    rw [List.mem_filter]
                    exact ⟨hi, by simp [hwin, hne]⟩
                  obtain ⟨⟨j, d⟩, hbest⟩ := Option.isSome_iff_exists.mp
                    (firstBest_isSome (fun (c b : Card T M C) =>
                      Decidable.decide (w.heldBy c.owner > w.heldBy b.owner) ||
                        (Decidable.decide (w.heldBy c.owner = w.heldBy b.owner) && Decidable.decide (c.turnAt < b.turnAt)))
                      _ (List.ne_nil_of_mem hwanted))
                  have hcl := claim_of_winner hwin hne
                  cases hfree : ((w.cards.zipIdx.map fun p => (p.2, p.1)).find? fun p => p.2.st = .down) with
                  | none => exact hdrain j d hbest hfree
                  | some p =>
                    obtain ⟨k, e⟩ := p
                    have hmem := List.mem_of_find?_eq_some hfree
                    have hp := List.find?_some hfree
                    have hdown : e.st = .down := by simpa using hp
                    rw [h2 ⟨e, List.mem_of_getElem? (mem_indexed.mp hmem), hdown⟩] at hcl
                    cases hcl
                refine ⟨?_, hmod⟩
                by_contra hne
                have := List.findSome?_eq_none_iff.mp hpass (i, c) hi
                simp [hwin, hne, hmod] at this

assert_no_sorry settled

end Timeshare
