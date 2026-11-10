/-
The measure behind the wait bound. For a flow (tenant `t`, model `m`) that
is waiting: how many tenants stand before `t`, and how many of `t`'s
models stand before `m`. While a turn is running, its tenant and its model
are counted as already gone to the back (that is where they go when it
ends): `pot l o x`, for a turn of tenant `o` on model `x`. Every lemma here
says that something the scheduler or the world does to the lines does not
raise the measure -- and that the start of a turn lowers it.
-/
import Timeshare.Proofs.Effect

namespace Timeshare

section lists
variable {α : Type} [DecidableEq α]

theorem before_length_lt {l : List α} {x : α} (hx : x ∈ l) : (before l x).length < l.length := by
  have h := List.takeWhile_append_dropWhile (p := fun y => Decidable.decide (y ≠ x)) (l := l)
  have hd : l.dropWhile (fun y => Decidable.decide (y ≠ x)) ≠ [] := by
    intro hnil
    rw [hnil, List.append_nil] at h
    have : x ∈ before l x := by unfold before; rw [h]; exact hx
    exact not_mem_before l x this
  have hlen := congrArg List.length h
  rw [List.length_append] at hlen
  have : 0 < (l.dropWhile (fun y => Decidable.decide (y ≠ x))).length := List.length_pos_iff.mpr hd
  unfold before
  omega

theorem length_filter_ne_lt {l : List α} {y : α} (hy : y ∈ l) :
    (l.filter (· ≠ y)).length + 1 ≤ l.length := by
  have : (l.filter (· ≠ y)).length < l.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨y, hy, by simp⟩
  omega

/-- The head of a line stands before everybody else in it. -/
theorem head_mem_before {y x : α} {l : List α} (hne : y ≠ x) : y ∈ before (y :: l) x := by
  simp [before, hne]

end lists

variable {T M : Type} [DecidableEq T] [DecidableEq M]

omit [DecidableEq M] in
@[simp] theorem tenantToBack_tenants (l : Lines T M) (o : Option T) :
    (l.tenantToBack o).tenants = match o with
      | some u => toBack l.tenants u
      | none => l.tenants := by
  cases o <;> rfl

omit [DecidableEq M] in
@[simp] theorem tenantToBack_models (l : Lines T M) (o : Option T) : (l.tenantToBack o).models = l.models := by
  cases o <;> rfl

@[simp] theorem ended_tenants (l : Lines T M) (o : Option T) (x : Option M) :
    (l.ended o x).tenants = (l.tenantToBack o).tenants := by
  cases x <;> rfl

@[simp] theorem ended_models (l : Lines T M) (o : Option T) (x : Option M) (v : T) :
    (l.ended o x).models v = match x with
      | some y => toBack (l.models v) y
      | none => l.models v := by
  cases x <;> cases o <;> rfl

/-- The tenants before `t`, not counting `o`, whose turn it is. If the turn
is `t`'s own, `t` will be last: `N - 1`, with `N` the most there can be in
the line. -/
def pEff (N : Nat) (t : T) (l : Lines T M) (o : Option T) : Nat :=
  if o = some t then N - 1 else ((before l.tenants t).filter fun u => some u ≠ o).length

/-- `t`'s models before `m`, not counting `x`, which is on the card. -/
def aEff (t : T) (m : M) (l : Lines T M) (x : Option M) : Nat :=
  ((before (l.models t) m).filter fun y => some y ≠ x).length

/-- The measure: at most this many more turns start before `m`'s. -/
def pot (N : Nat) (t : T) (m : M) (l : Lines T M) (o : Option T) (x : Option M) : Nat :=
  aEff t m l x * N + pEff N t l o

omit [DecidableEq M] in
theorem pEff_le {N : Nat} {t : T} {l : Lines T M} (o : Option T) (hN : l.tenants.length ≤ N)
    (ht : t ∈ l.tenants) : pEff N t l o ≤ N - 1 := by
  unfold pEff
  split
  · exact le_rfl
  · have h1 := List.length_filter_le (fun u => Decidable.decide (some u ≠ o)) (before l.tenants t)
    have h2 := before_length_lt ht
    omega

/-- **The end of a turn** does not raise the measure: its tenant and model
go to the back, where they were counted already. -/
theorem pot_ended {N : Nat} {t : T} {m : M} {l : Lines T M} {o : Option T} {x : Option M}
    (hn : l.Nodup) (ht : t ∈ l.tenants) (hm : m ∈ l.models t) (hx : x ≠ some m)
    (hN : l.tenants.length ≤ N) : pot N t m (l.ended o x) none none ≤ pot N t m l o x := by
  have ha : aEff t m (l.ended o x) none ≤ aEff t m l x := by
    unfold aEff
    cases x with
    | none => simp
    | some y =>
      have hy : y ≠ m := fun h => hx (h ▸ rfl)
      simp only [ended_models, before_toBack (hn.2 t) hm hy]
      simp
  have hp : pEff N t (l.ended o x) none ≤ pEff N t l o := by
    cases o with
    | none => simp [pEff]
    | some u =>
      by_cases hu : u = t
      · subst hu
        have h1 : pEff N u l (some u) = N - 1 := by simp [pEff]
        rw [h1]
        refine pEff_le none ?_ ?_
        · simpa [(toBack_perm l.tenants u).length_eq] using hN
        · simpa using ht
      · simp only [pEff, ended_tenants, tenantToBack_tenants, before_toBack hn.1 ht hu]
        simp [hu]
  unfold pot
  exact Nat.add_le_add (Nat.mul_le_mul_right N ha) hp

/-- **A turn that changes hands** lowers the measure: the tenant it goes to
stood before `t` (or it was `t`'s own turn), and is counted as gone now. -/
theorem pot_pass {N : Nat} {t : T} {m : M} {l : Lines T M} {o : Option T} {x : Option M} {u : T}
    (hn : l.Nodup) (ht : t ∈ l.tenants) (hu : u ≠ t) (hul : u ∈ l.tenants) (huo : some u ≠ o)
    (hfirst : o = some t ∨ u ∈ before l.tenants t) (hN : l.tenants.length ≤ N) :
    pot N t m (l.tenantToBack o) (some u) x + 1 ≤ pot N t m l o x := by
  have ha : aEff t m (l.tenantToBack o) x = aEff t m l x := by simp [aEff]
  have hne : ¬ (some u = some t) := fun h => hu (Option.some.inj h)
  have hp : pEff N t (l.tenantToBack o) (some u) + 1 ≤ pEff N t l o := by
    cases o with
    | none =>
      have hb : u ∈ before l.tenants t := by
        rcases hfirst with h | h
        · cases h
        · exact h
      have := length_filter_ne_lt hb
      simpa [pEff, hne] using this
    | some v =>
      by_cases hv : v = t
      · subst hv
        have h1 : pEff N v l (some v) = N - 1 := by simp [pEff]
        have hmem : u ∈ l.tenants.erase v := (List.Nodup.mem_erase_iff hn.1).mpr ⟨hu, hul⟩
        have h2 := length_filter_ne_lt hmem
        have h3 : (l.tenants.erase v).length = l.tenants.length - 1 := List.length_erase_of_mem ht
        have h4 := List.length_pos_of_mem ht
        rw [h1]
        simp only [pEff, hne, ite_false, tenantToBack_tenants, before_toBack_self hn.1 ht]
        have h5 : ((l.tenants.erase v).filter fun w => Decidable.decide (some w ≠ some u)).length =
            ((l.tenants.erase v).filter (· ≠ u)).length := by simp
        omega
      · have hne' : ¬ (some v = some t) := fun h => hv (Option.some.inj h)
        have huv : u ≠ v := fun h => huo (h ▸ rfl)
        have hb : u ∈ before l.tenants t := by
          rcases hfirst with h | h
          · exact absurd h hne'
          · exact h
        have hmem : u ∈ (before l.tenants t).filter (· ≠ v) := List.mem_filter.mpr ⟨hb, by simpa using huv⟩
        have := length_filter_ne_lt hmem
        simp only [pEff, hne, hne', ite_false, tenantToBack_tenants, before_toBack hn.1 ht hv]
        have h5 : ∀ (s : List T), (s.filter fun w => Decidable.decide (some w ≠ some u)).length =
            (s.filter (· ≠ u)).length := by intro s; simp
        have h6 : ∀ (s : List T), (s.filter fun w => Decidable.decide (some w ≠ some v)).length =
            (s.filter (· ≠ v)).length := by intro s; simp
        rw [h5, h6]
        exact this
  unfold pot
  rw [ha]
  omega

/-- **New requests** do not raise the measure: newcomers join behind. -/
theorem pot_join {N : Nat} {t : T} {m : M} {l : Lines T M} {flows : List (Flow T M)} (o : Option T)
    (x : Option M) (hn : l.Nodup) (ht : t ∈ l.tenants) (hm : m ∈ l.models t)
    (hq : hasFlow flows t m = true) : pot N t m (l.join flows) o x ≤ pot N t m l o x := by
  have hqt : hasQueued flows t = true := by
    simp only [hasFlow, hasQueued, List.any_eq_true, decide_eq_true_eq] at hq ⊢
    obtain ⟨f, hf, h1, _⟩ := hq
    exact ⟨f, hf, h1⟩
  have ha : aEff t m (l.join flows) x ≤ aEff t m l x := by
    unfold aEff
    rw [before_join_models (hn.2 t) ht hm hq]
    exact (List.filter_sublist.filter _).length_le
  have hp : pEff N t (l.join flows) o ≤ pEff N t l o := by
    unfold pEff
    split
    · exact le_rfl
    · rw [before_join_tenants hn.1 ht hqt]
      exact (List.filter_sublist.filter _).length_le
  unfold pot
  exact Nat.add_le_add (Nat.mul_le_mul_right N ha) hp

/-- **The start of a turn** lowers the measure: the first tenant in line
starts its first model, and that is not `t` starting `m`. -/
theorem pot_start {N : Nat} {t : T} {m : M} {l : Lines T M} {o : T} {x : M} {ts : List T} {ms : List M}
    (hts : l.tenants = o :: ts) (hms : l.models o = x :: ms) (ht : t ∈ l.tenants) (hx : x ≠ m)
    (hN : l.tenants.length ≤ N) : pot N t m l (some o) (some x) + 1 ≤ pot N t m l none none := by
  have hN1 : 1 ≤ N := by rw [hts] at hN; simp at hN; omega
  have ha : aEff t m l (some x) ≤ aEff t m l none := by
    unfold aEff
    exact (List.monotone_filter_right _ fun y hy => by simp at hy ⊢).length_le
  by_cases ho : o = t
  · subst ho
    have ha' : aEff o m l (some x) + 1 ≤ aEff o m l none := by
      unfold aEff
      rw [hms]
      have hmem : x ∈ before (x :: ms) m := head_mem_before hx
      have := length_filter_ne_lt hmem
      simpa using this
    have hp : pEff N o l (some o) = N - 1 := by simp [pEff]
    unfold pot
    rw [hp]
    have : (aEff o m l (some x) + 1) * N ≤ aEff o m l none * N := Nat.mul_le_mul_right N ha'
    have h2 : (aEff o m l (some x) + 1) * N = aEff o m l (some x) * N + N := by ring
    omega
  · have hp : pEff N t l (some o) + 1 ≤ pEff N t l none := by
      have hne : ¬ (some o = some t) := fun h => ho (Option.some.inj h)
      simp only [pEff, hne, ite_false]
      rw [hts]
      have hmem : o ∈ before (o :: ts) t := head_mem_before ho
      have := length_filter_ne_lt hmem
      simpa using this
    unfold pot
    have := Nat.mul_le_mul_right N ha
    omega

assert_no_sorry pot_ended
assert_no_sorry pot_pass
assert_no_sorry pot_join
assert_no_sorry pot_start

end Timeshare
