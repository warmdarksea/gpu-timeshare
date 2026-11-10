/-
The lines: what `toBack`, `Lines.ended` and `Lines.join` do to who stands
before whom. `before l x` is what stands before `x` in `l`; the wait bound
is a count of it.
-/
import Mathlib.Data.List.TakeWhile
import Timeshare.Proofs.Step

namespace Timeshare

section lists
variable {α : Type} [DecidableEq α]

/-- What stands before `x` in `l`. -/
def before (l : List α) (x : α) : List α := l.takeWhile (· ≠ x)

theorem toBack_perm (s : List α) (x : α) : (toBack s x).Perm s := by
  unfold toBack
  split
  · rename_i h
    exact List.perm_append_comm.trans (List.perm_cons_erase h).symm
  · rfl

theorem toBack_nodup {s : List α} (x : α) (h : s.Nodup) : (toBack s x).Nodup :=
  (toBack_perm s x).nodup_iff.mpr h

@[simp] theorem mem_toBack {s : List α} {x y : α} : y ∈ toBack s x ↔ y ∈ s :=
  (toBack_perm s x).mem_iff

theorem before_sublist (l : List α) (x : α) : (before l x).Sublist l :=
  List.takeWhile_sublist _

theorem not_mem_before (l : List α) (x : α) : x ∉ before l x := by
  intro h
  have := List.mem_takeWhile_imp h
  simp at this

theorem before_append_of_mem {l : List α} (r : List α) {x : α} (hx : x ∈ l) : before (l ++ r) x = before l x := by
  induction l with
  | nil => simp at hx
  | cons z zs ih =>
    by_cases hzx : z = x
    · simp [before, hzx]
    · have hx' : x ∈ zs := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hzx
        · exact h
      have := ih hx'
      unfold before at this ⊢
      simpa [hzx] using this

/-- Sending somebody else to the back takes them from before `x`, and
nobody else. -/
theorem before_toBack {s : List α} {x y : α} (hs : s.Nodup) (hx : x ∈ s) (hne : y ≠ x) :
    before (toBack s y) x = (before s x).filter (· ≠ y) := by
  induction s with
  | nil => simp at hx
  | cons z zs ih =>
    have hz : z ∉ zs := (List.nodup_cons.mp hs).1
    have hzs : zs.Nodup := (List.nodup_cons.mp hs).2
    by_cases hzx : z = x
    · subst hzx
      have : ¬ z = y := fun h => hne h.symm
      by_cases hy : y ∈ zs <;> simp [toBack, before, hy, this, hne]
    · have hx' : x ∈ zs := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hzx
        · exact h
      by_cases hzy : z = y
      · subst hzy
        have hb : ∀ a ∈ before zs x, a ≠ z := fun a ha h => hz (h ▸ (before_sublist zs x).subset ha)
        have h1 : before (zs ++ [z]) x = before zs x := before_append_of_mem _ hx'
        simp only [toBack, List.mem_cons, true_or, ite_true, List.erase_cons_head, h1]
        rw [show before (z :: zs) x = z :: before zs x by simp [before, hzx]]
        simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, not_false_eq_true,
          List.filter_cons_of_neg]
        exact (List.filter_eq_self.mpr fun a ha => by simpa using hb a ha).symm
      · have h1 : toBack (z :: zs) y = z :: toBack zs y := by
          unfold toBack
          by_cases hy : y ∈ zs
          · have : y ∈ z :: zs := List.mem_cons_of_mem _ hy
            simp [hy, this, hzy]
          · have : y ∉ z :: zs := by simp [hy, Ne.symm hzy]
            simp [hy, this]
        rw [h1]
        have ih' := ih hzs hx'
        unfold before at ih' ⊢
        simpa [hzx, hzy] using ih'

/-- Whoever goes to the back has everybody else before them. -/
theorem before_toBack_self {s : List α} {x : α} (hs : s.Nodup) (hx : x ∈ s) : before (toBack s x) x = s.erase x := by
  have hnot : x ∉ s.erase x := fun h => (List.Nodup.mem_erase_iff hs).mp h |>.1 rfl
  unfold toBack before
  rw [ite_eq_left hx, List.takeWhile_append_of_pos]
  · simp
  · intro a ha
    have : a ≠ x := fun h => hnot (h ▸ ha)
    simpa using this

/-- A line splits at `x`: what stands before it, `x`, and the rest. -/
theorem before_split : ∀ {l : List α} {x : α}, x ∈ l → ∃ r, l = before l x ++ x :: r
  | [], _, h => by simp at h
  | z :: zs, x, h => by
    by_cases hzx : z = x
    · exact ⟨zs, by simp [before, hzx]⟩
    · have hx : x ∈ zs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hzx
        · exact h
      obtain ⟨r, hr⟩ := before_split hx
      refine ⟨r, ?_⟩
      have : before (z :: zs) x = z :: before zs x := by simp [before, hzx]
      rw [this, List.cons_append, ← hr]

/-! ### `eraseDups` -/

theorem eraseDups_of_nodup : ∀ {l : List α}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: as, h => by
    have ha : a ∉ as := (List.nodup_cons.mp h).1
    have has : as.Nodup := (List.nodup_cons.mp h).2
    rw [List.eraseDups_cons]
    have : as.filter (fun b => !b == a) = as :=
      List.filter_eq_self.mpr fun b hb => by
        have : b ≠ a := fun h => ha (h ▸ hb)
        simpa using this
    rw [this, eraseDups_of_nodup has]

theorem nodup_eraseDups (l : List α) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨?_, ih _ ?_ _ rfl⟩
      · simp
      · have := List.length_filter_le (fun b => !b == a) as
        simp only [List.length_cons] at h
        omega

omit [DecidableEq α] in
theorem takeWhile_congr_mem {p q : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.takeWhile p = l.takeWhile q
  | [], _ => rfl
  | a :: as, h => by
    have ha := h a (List.mem_cons_self ..)
    have ih := takeWhile_congr_mem (l := as) fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp [List.takeWhile_cons, ha, ih]

/-- Dropping some of a line and letting newcomers join at the back leaves
before `x` those who were before it, less the ones dropped. -/
theorem before_join {l : List α} (p : α → Bool) (new : List α) {x : α} (hl : l.Nodup) (hx : x ∈ l)
    (hp : p x = true) : before ((l.filter p ++ new).eraseDups) x = (before l x).filter p := by
  rw [List.eraseDups_append, eraseDups_of_nodup (hl.filter _),
    before_append_of_mem _ (List.mem_filter.mpr ⟨hx, hp⟩)]
  unfold before
  rw [List.takeWhile_filter]
  congr 1
  apply takeWhile_congr_mem
  intro a _
  by_cases ha : a = x
  · subst ha; simp [hp]
  · simp [ha]

end lists

variable {T M : Type} [DecidableEq T] [DecidableEq M]

/-! ### The lines -/

/-- Nobody stands in a line twice. -/
def Lines.Nodup (l : Lines T M) : Prop := l.tenants.Nodup ∧ ∀ t, (l.models t).Nodup

/-- The flows that count: the ones with something queued, oldest first. -/
def queuedFlows (flows : List (Flow T M)) : List (Flow T M) :=
  (flows.mergeSort fun a b => a.oldest ≤ b.oldest).filter fun f => f.queued > 0

omit [DecidableEq T] [DecidableEq M] in
theorem mem_queuedFlows {flows : List (Flow T M)} {f : Flow T M} :
    f ∈ queuedFlows flows ↔ f ∈ flows ∧ f.queued > 0 := by
  simp [queuedFlows, List.mem_mergeSort]

/-- Tenant `t` has something queued. -/
def hasQueued (flows : List (Flow T M)) (t : T) : Bool := (queuedFlows flows).any fun f => f.tenant = t

/-- Tenant `t` has something queued for model `m`. -/
def hasFlow (flows : List (Flow T M)) (t : T) (m : M) : Bool :=
  (queuedFlows flows).any fun f => f.tenant = t ∧ f.model = m

theorem join_tenants (l : Lines T M) (flows : List (Flow T M)) :
    (l.join flows).tenants =
      (l.tenants.filter (hasQueued flows) ++ (queuedFlows flows).map (·.tenant)).eraseDups := rfl

theorem join_models (l : Lines T M) (flows : List (Flow T M)) (t : T) :
    (l.join flows).models t =
      (((if t ∈ l.tenants then l.models t else []).filter (hasFlow flows t)) ++
        ((queuedFlows flows).filter fun f => f.tenant = t).map (·.model)).eraseDups := rfl

/-- After `join`, nobody stands in a line twice. -/
theorem join_nodup (l : Lines T M) (flows : List (Flow T M)) : (l.join flows).Nodup :=
  ⟨by rw [join_tenants]; exact nodup_eraseDups _, fun t => by rw [join_models]; exact nodup_eraseDups _⟩

/-- After `join`, the line is the tenants with something queued. -/
theorem mem_join_tenants {l : Lines T M} {flows : List (Flow T M)} {t : T} :
    t ∈ (l.join flows).tenants ↔ hasQueued flows t = true := by
  rw [join_tenants, List.mem_eraseDups, List.mem_append, List.mem_filter, List.mem_map]
  simp only [hasQueued, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro (⟨_, h⟩ | ⟨f, hf, rfl⟩)
    · exact h
    · exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact Or.inr ⟨f, hf, rfl⟩

/-- After `join`, a tenant's line is its models with something queued. -/
theorem mem_join_models {l : Lines T M} {flows : List (Flow T M)} {t : T} {m : M} :
    m ∈ (l.join flows).models t ↔ hasFlow flows t m = true := by
  rw [join_models, List.mem_eraseDups, List.mem_append, List.mem_filter, List.mem_map]
  simp only [hasFlow, List.any_eq_true, decide_eq_true_eq, List.mem_filter]
  constructor
  · rintro (⟨_, h⟩ | ⟨f, ⟨hf, rfl⟩, rfl⟩)
    · exact h
    · exact ⟨f, hf, rfl, rfl⟩
  · rintro ⟨f, hf, rfl, rfl⟩
    exact Or.inr ⟨f, ⟨hf, rfl⟩, rfl⟩

/-- `join` lets nobody in before a tenant that was in the line already. -/
theorem before_join_tenants {l : Lines T M} {flows : List (Flow T M)} {t : T} (hl : l.tenants.Nodup)
    (ht : t ∈ l.tenants) (hq : hasQueued flows t = true) :
    before (l.join flows).tenants t = (before l.tenants t).filter (hasQueued flows) := by
  rw [join_tenants]
  exact before_join _ _ hl ht hq

/-- `join` lets no model in before one that was in its tenant's line already. -/
theorem before_join_models {l : Lines T M} {flows : List (Flow T M)} {t : T} {m : M}
    (hl : (l.models t).Nodup) (ht : t ∈ l.tenants) (hm : m ∈ l.models t) (hq : hasFlow flows t m = true) :
    before ((l.join flows).models t) m = (before (l.models t) m).filter (hasFlow flows t) := by
  rw [join_models, ite_eq_left ht]
  exact before_join _ _ hl hm hq

omit [DecidableEq M] in
theorem tenantToBack_nodup {l : Lines T M} (t : Option T) (h : l.Nodup) : (l.tenantToBack t).Nodup := by
  cases t with
  | none => exact h
  | some t => exact ⟨toBack_nodup _ h.1, h.2⟩

theorem ended_nodup {l : Lines T M} (t : Option T) (m : Option M) (h : l.Nodup) : (l.ended t m).Nodup := by
  have h' := tenantToBack_nodup t h
  cases m with
  | none => exact h'
  | some m => exact ⟨h'.1, fun u => toBack_nodup _ (h'.2 u)⟩

assert_no_sorry before_toBack
assert_no_sorry before_join_tenants
assert_no_sorry before_join_models
assert_no_sorry join_nodup

end Timeshare
