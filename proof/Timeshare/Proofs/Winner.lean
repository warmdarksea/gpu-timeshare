/-
Who wins a card: `firstLowest`, which `winner` and `claim` both are, finds
the first tenant of the lowest rank among those with a pick.
-/
import Timeshare.Proofs.Potential

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

section firstLowest
variable {α β : Type} (pick : α → Option β) (rank : α → Nat)

/-- One step of `firstLowest`. -/
def flStep (best : Option (α × β)) (t : α) : Option (α × β) :=
  match pick t, best with
  | some m, none => some (t, m)
  | some m, some b => if rank t < rank b.1 then some (t, m) else some b
  | none, _ => best

theorem firstLowest_eq (l : List α) : firstLowest pick rank l = l.foldl (flStep pick rank) none := rfl

variable {pick rank}

theorem flStep_none {t : α} (best : Option (α × β)) (h : pick t = none) : flStep pick rank best t = best := by
  simp [flStep, h]

theorem flStep_first {t : α} {m : β} (h : pick t = some m) : flStep pick rank none t = some (t, m) := by
  simp [flStep, h]

theorem flStep_some {t : α} {m : β} (b : α × β) (h : pick t = some m) :
    flStep pick rank (some b) t = if rank t < rank b.1 then some (t, m) else some b := by
  simp [flStep, h]

/-- Nobody takes the place of somebody of rank 0. -/
theorem flStep_fixed (b : α × β) (t : α) (h : ¬ rank t < rank b.1) : flStep pick rank (some b) t = some b := by
  cases hp : pick t with
  | none => exact flStep_none _ hp
  | some m => rw [flStep_some _ hp, ite_eq_right h]

theorem foldl_fixed {γ : Type} (f : γ → α → γ) (b : γ) :
    ∀ (l : List α), (∀ t ∈ l, f b t = b) → l.foldl f b = b := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    rw [List.foldl_cons, h a (List.mem_cons_self ..)]
    exact ih fun t ht => h t (List.mem_cons_of_mem _ ht)

theorem foldl_flStep_some : ∀ (l : List α) (init : Option (α × β)) (r : α × β),
    l.foldl (flStep pick rank) init = some r → init = some r ∨ (r.1 ∈ l ∧ pick r.1 = some r.2) := by
  intro l
  induction l with
  | nil => intro init r h; left; simpa using h
  | cons a as ih =>
    intro init r h
    rw [List.foldl_cons] at h
    rcases ih _ _ h with h1 | ⟨h1, h2⟩
    · cases hp : pick a with
      | none => left; rw [flStep_none _ hp] at h1; exact h1
      | some m =>
        cases init with
        | none =>
          rw [flStep_first hp] at h1
          cases h1
          right; exact ⟨List.mem_cons_self .., hp⟩
        | some b =>
          rw [flStep_some _ hp] at h1
          split at h1
          · cases h1
            right; exact ⟨List.mem_cons_self .., hp⟩
          · left; exact h1
    · right; exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- Whoever `firstLowest` finds is in the line, with their own pick. -/
theorem firstLowest_some {l : List α} {u : α} {mu : β} (h : firstLowest pick rank l = some (u, mu)) :
    u ∈ l ∧ pick u = some mu := by
  rcases foldl_flStep_some l none (u, mu) h with h1 | h1
  · cases h1
  · exact h1

/-- If the first in line has a pick and nobody after has a lower rank, it
is the first in line that `firstLowest` finds. -/
theorem firstLowest_head {o : α} {x : β} {ts : List α} (hp : pick o = some x)
    (hr : ∀ u ∈ ts, ¬ rank u < rank o) : firstLowest pick rank (o :: ts) = some (o, x) := by
  rw [firstLowest_eq, List.foldl_cons, flStep_first hp]
  exact foldl_fixed _ _ _ fun u hu => flStep_fixed _ _ (hr u hu)

/-- If `t` has a pick and rank 0, `firstLowest` finds `t` or somebody
before it in the line, of rank 0 too. -/
theorem firstLowest_first [DecidableEq α] {l : List α} {t u : α} {mu : β} (ht : t ∈ l)
    (hp : (pick t).isSome = true) (h0 : rank t = 0) (h : firstLowest pick rank l = some (u, mu)) :
    (u = t ∨ u ∈ before l t) ∧ rank u = 0 := by
  obtain ⟨rest, hsplit⟩ := before_split ht
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp hp
  rw [firstLowest_eq, hsplit, List.foldl_append, List.foldl_cons] at h
  have fixed : ∀ b : α × β, rank b.1 = 0 → rest.foldl (flStep pick rank) (some b) = some b :=
    fun b hb => foldl_fixed _ _ _ fun v _ => flStep_fixed _ _ (by omega)
  cases h1 : (before l t).foldl (flStep pick rank) none with
  | none =>
    rw [h1, flStep_first hmt, fixed (t, mt) h0] at h
    cases h
    exact ⟨Or.inl rfl, h0⟩
  | some b =>
    have hb : b.1 ∈ before l t := by
      rcases foldl_flStep_some _ none b h1 with h2 | h2
      · cases h2
      · exact h2.1
    rw [h1, flStep_some _ hmt] at h
    split at h
    · rw [fixed (t, mt) h0] at h
      cases h
      exact ⟨Or.inl rfl, h0⟩
    · rename_i hnot
      have hb0 : rank b.1 = 0 := by omega
      rw [fixed b hb0] at h
      cases h
      exact ⟨Or.inr hb, hb0⟩

/-- If anybody in the line has a pick, `firstLowest` finds somebody. -/
theorem foldl_flStep_isSome : ∀ (l : List α) (init : Option (α × β)),
    (init.isSome = true ∨ ∃ t ∈ l, (pick t).isSome = true) →
    (l.foldl (flStep pick rank) init).isSome = true := by
  intro l
  induction l with
  | nil =>
    intro init h
    rcases h with h | ⟨t, ht, _⟩
    · simpa using h
    · simp at ht
  | cons a as ih =>
    intro init h
    rw [List.foldl_cons]
    by_cases hs : (flStep pick rank init a).isSome = true
    · exact ih _ (Or.inl hs)
    · refine ih _ (Or.inr ?_)
      rcases h with h | ⟨t, ht, hpt⟩
      · exfalso
        apply hs
        obtain ⟨b, rfl⟩ := Option.isSome_iff_exists.mp h
        cases hp : pick a with
        | none => rw [flStep_none _ hp]; rfl
        | some m => rw [flStep_some _ hp]; split <;> rfl
      · rcases List.mem_cons.mp ht with rfl | ht'
        · exfalso
          apply hs
          obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hpt
          cases init with
          | none => rw [flStep_first hm]; rfl
          | some b => rw [flStep_some _ hm]; split <;> rfl
        · exact ⟨t, ht', hpt⟩

theorem firstLowest_isSome {l : List α} {t : α} (ht : t ∈ l) (hp : (pick t).isSome = true) :
    (firstLowest pick rank l).isSome = true :=
  foldl_flStep_isSome l none (Or.inr ⟨t, ht, hp⟩)

end firstLowest

/-- A tenant with a lost model wins a card only to move that model there. -/
theorem winner_lost {w : World T M C} {c : Card T M C} {t : T} {m m' : M}
    (h : w.winner c = some (t, m)) (hl : w.lost t = some m') : m = m' := by
  unfold World.winner at h
  split at h
  · cases h
  · have := (firstLowest_some h).2
    unfold World.pick at this
    rw [hl] at this
    simpa using this.symm

/-- The winner is in the line. -/
theorem winner_mem {w : World T M C} {c : Card T M C} {t : T} {m : M} (h : w.winner c = some (t, m)) :
    t ∈ w.lines.tenants := by
  unfold World.winner at h
  split at h
  · cases h
  · exact (firstLowest_some h).1

/-- A tenant with a lost model and no card wins any card whose turn is
old -- unless somebody before it in the line does, who has no card either
and is not the owner. -/
theorem winner_first {w : World T M C} {c : Card T M C} {t u : T} {mu : M}
    (h : w.winner c = some (u, mu)) (ht : t ∈ w.lines.tenants) (hl : (w.lost t).isSome = true)
    (hown : some t ≠ c.owner) (hheld : w.held t = 0) :
    (u = t ∨ u ∈ before w.lines.tenants t) ∧ w.rank c u = 0 := by
  unfold World.winner at h
  split at h
  · cases h
  · refine firstLowest_first ht ?_ ?_ h
    · obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hl
      simp [World.pick, hm']
    · simp [World.rank, hown, hheld]

/-- A tenant with a lost model has a claim to any card whose turn is old:
somebody wins it. -/
theorem winner_isSome {w : World T M C} {c : Card T M C} {t : T} (hst : c.st = .up)
    (hq : w.pol.quantum c ≤ w.now - c.turnAt) (hnew : c.turnAt < w.now) (ht : t ∈ w.lines.tenants)
    (hl : (w.lost t).isSome = true) : (w.winner c).isSome = true := by
  unfold World.winner
  rw [ite_eq_right (by rintro (h | h | h) <;> first | exact h hst | omega)]
  refine firstLowest_isSome ht ?_
  obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hl
  simp [World.pick, hm']

omit [DecidableEq T] in
theorem lost_not_placed {w : World T M C} {t : T} {m : M} (h : w.lost t = some m) : w.placed m = false := by
  unfold World.lost at h
  have := List.find?_some h
  simpa using this

/-- `firstLowest` finds nobody of a higher rank than anybody with a pick. -/
theorem firstLowest_le {α β : Type} {pick : α → Option β} {rank : α → Nat} :
    ∀ (l : List α) (init : Option (α × β)) (r : α × β),
      l.foldl (flStep pick rank) init = some r →
      (∀ b, init = some b → rank r.1 ≤ rank b.1) ∧ ∀ t ∈ l, (pick t).isSome = true → rank r.1 ≤ rank t := by
  intro l
  induction l with
  | nil =>
    intro init r h
    simp only [List.foldl_nil] at h
    exact ⟨fun b hb => by rw [h] at hb; cases hb; exact le_rfl, fun t ht => by simp at ht⟩
  | cons a as ih =>
    intro init r h
    rw [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := ih _ _ h
    -- the step keeps the best so far or takes `a`, whichever is lower
    have hstep : (∀ b, init = some b → ∃ b', flStep pick rank init a = some b' ∧ rank b'.1 ≤ rank b.1) ∧
        ((pick a).isSome = true → ∃ b', flStep pick rank init a = some b' ∧ rank b'.1 ≤ rank a) := by
      cases hp : pick a with
      | none =>
        refine ⟨fun b hb => ⟨b, by rw [flStep_none _ hp, hb], le_rfl⟩, fun h => by simp at h⟩
      | some m =>
        cases init with
        | none =>
          exact ⟨fun b hb => (by cases hb), fun _ => ⟨(a, m), flStep_first hp, le_rfl⟩⟩
        | some b0 =>
          rw [flStep_some _ hp]
          by_cases hlt : rank a < rank b0.1
          · simp only [hlt, ite_true]
            refine ⟨fun b hb => ?_, fun _ => ⟨(a, m), rfl, le_rfl⟩⟩
            cases hb
            exact ⟨(a, m), rfl, Nat.le_of_lt hlt⟩
          · simp only [hlt, ite_false]
            refine ⟨fun b hb => ?_, fun _ => ⟨b0, rfl, Nat.le_of_not_lt hlt⟩⟩
            cases hb
            exact ⟨b0, rfl, le_rfl⟩
    refine ⟨fun b hb => ?_, fun t ht hpt => ?_⟩
    · obtain ⟨b', hb', hle⟩ := hstep.1 b hb
      exact le_trans (h1 b' hb') hle
    · rcases List.mem_cons.mp ht with rfl | ht'
      · obtain ⟨b', hb', hle⟩ := hstep.2 hpt
        exact le_trans (h1 b' hb') hle
      · exact h2 t ht' hpt

/-- Whoever wins a card has no higher rank than any tenant with a pick. -/
theorem winner_le {w : World T M C} {c : Card T M C} {t u : T} {mu : M}
    (h : w.winner c = some (u, mu)) (ht : t ∈ w.lines.tenants) (hl : (w.lost t).isSome = true) :
    w.rank c u ≤ w.rank c t := by
  unfold World.winner at h
  split at h
  · cases h
  · refine (firstLowest_le _ none (u, mu) h).2 t ht ?_
    obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hl
    simp [World.pick, hm']

theorem run_some {w w' : World T M C} {a : Action T M C} (n : Nat) (hr : w.rule = some (a, w')) :
    w.run (n + 1) = (a :: (w'.run n).1, (w'.run n).2) := by
  simp [World.run, hr]

theorem run_none {w : World T M C} (n : Nat) (hr : w.rule = none) : w.run (n + 1) = ([], w) := by
  simp [World.run, hr]

end Timeshare
