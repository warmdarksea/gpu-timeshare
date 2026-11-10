/-
Any number of cards: what each kind of change to one card does to the
measure of Multi.lean.

- `mpot_congr`: a change the measure does not see (requests come and go, a
  load finishes, a drained card stops, a card that drained for somebody
  starts their model).
- `mpot_ended` (Multi.lean): a turn ends.
- `mpot_start`: a card that was nobody's becomes somebody's.
- `mpot_pass`: a turn changes hands, the model stays.

A drain is the last two at once: the old turn ends, and the card is the
winner's from then on.
-/
import Timeshare.Proofs.Multi

namespace Timeshare

theorem any_set_congr {α : Type} (P : α → Bool) : ∀ (l : List α) (i : Nat) (c c' : α), l[i]? = some c →
    P c' = P c → (l.set i c').any P = l.any P := by
  intro l
  induction l with
  | nil => intro i c c' h; simp at h
  | cons z zs ih =>
    intro i c c' h hp
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [hp]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simp [ih i c c' h hp]

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

section multi
variable (N : Nat) (t : T) (m : M)

/-- A card changes in a way the measure does not see: it is the same
tenant's as before, with the same model (on it, or coming). -/
theorem mpot_congr {cards : List (Card T M C)} {l : Lines T M} {i : Nat} {c : Card T M C} (c' : Card T M C)
    (hw : MWaiting N t m cards l) (hi : cards[i]? = some c)
    (hwho : ∀ v, (c'.taken && Decidable.decide (c'.owner = some v)) =
      (c.taken && Decidable.decide (c.owner = some v)))
    (hhas : ∀ y, c'.has y = c.has y) :
    MWaiting N t m (cards.set i c') l ∧ mPot N t m (cards.set i c') l = mPot N t m cards l := by
  have hheld : ∀ v, heldIn (cards.set i c') v = heldIn cards v := by
    intro v
    have := heldIn_set c' v hi
    rw [hwho v] at this
    omega
  have hplaced : ∀ y, placedIn (cards.set i c') y = placedIn cards y := fun y =>
    any_set_congr _ cards i c c' hi (hhas y)
  refine ⟨⟨hw.nodup, hw.tenant, hw.model, hw.few, ?_⟩, ?_⟩
  · intro d hd
    rcases List.mem_or_eq_of_mem_set hd with h1 | h1
    · exact hw.away d h1
    · rw [h1, hhas]
      exact hw.away c (List.mem_of_getElem? hi)
  · unfold mPot
    rw [show heldIn (cards.set i c') = heldIn cards from funext hheld,
      show placedIn (cards.set i c') = placedIn cards from funext hplaced]

/-- What it does to the cards the measure counts, when a card that was
nobody's becomes `u`'s, for `x`. -/
theorem start_facts {cards : List (Card T M C)} {i : Nat} {c c' : Card T M C} {u : T} {x : M}
    (hi : cards[i]? = some c) (hc : c.taken = false) (hc' : c'.taken = true) (ho : c'.owner = some u)
    (hx : c'.has x = true) :
    (∀ v, heldIn (cards.set i c') v = heldIn cards v + (if u = v then 1 else 0)) ∧
    (∀ y, placedIn (cards.set i c') y = false → placedIn cards y = false) ∧
    placedIn (cards.set i c') x = true := by
  refine ⟨fun v => ?_, fun y hp => ?_, ?_⟩
  · have := heldIn_set c' v hi
    simp only [hc, hc', ho, Bool.false_and, Bool.true_and, Bool.false_eq_true, ite_false,
      decide_eq_true_eq, Option.some.injEq] at this
    omega
  · by_contra hpl
    have hpl' : placedIn cards y = true := by simpa using hpl
    have : placedIn (cards.set i c') y = true :=
      any_of_set _ cards i c c' hi (has_of_not_taken hc y) hpl'
    rw [hp] at this
    cases this
  · unfold placedIn
    rw [List.any_eq_true]
    refine ⟨c', ?_, hx⟩
    have hlt : i < cards.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hi
      cases hi
    exact List.mem_iff_getElem?.mpr ⟨i, by simp [hlt]⟩

/-- **A card that was nobody's becomes `u`'s**, for a model `x` other than
`m`: the flow still waits. The measure is no higher if `u` is not `t`; it
is lower if `t` holds no card and `u` stood before it in the line holding
none either, and if `u` is `t` and `x` stood before `m` in its line, on no
card. -/
theorem mpot_start {cards : List (Card T M C)} {l : Lines T M} {i : Nat} {c c' : Card T M C} {u : T} {x : M}
    (hw : MWaiting N t m cards l) (hi : cards[i]? = some c) (hc : c.taken = false)
    (hc' : c'.taken = true) (ho : c'.owner = some u) (hx : c'.has x = true) (hm : c'.has m = false) :
    MWaiting N t m (cards.set i c') l ∧
      (u ≠ t → mPot N t m (cards.set i c') l ≤ mPot N t m cards l) ∧
      (u ≠ t → heldIn cards t = 0 → u ∈ before l.tenants t → heldIn cards u = 0 →
        mPot N t m (cards.set i c') l + 1 ≤ mPot N t m cards l) ∧
      (u = t → x ∈ before (l.models t) m → placedIn cards x = false →
        mPot N t m (cards.set i c') l + 1 ≤ mPot N t m cards l) := by
  obtain ⟨hheld, hplaced, hxp⟩ := start_facts hi hc hc' ho hx
  have ha : aPart m (l.models t) (placedIn (cards.set i c')) ≤ aPart m (l.models t) (placedIn cards) :=
    aPart_le m (List.Sublist.refl _) fun y _ => hplaced y
  refine ⟨⟨hw.nodup, hw.tenant, hw.model, hw.few, ?_⟩, ?_, ?_, ?_⟩
  · intro d hd
    rcases List.mem_or_eq_of_mem_set hd with h1 | h1
    · exact hw.away d h1
    · rw [h1]; exact hm
  · intro hut
    have hp : pPart N t l.tenants (heldIn (cards.set i c')) ≤ pPart N t l.tenants (heldIn cards) :=
      pPart_le N t (List.Sublist.refl _) (fun w _ hw0 => by rw [hheld w] at hw0; omega) hw.tenant hw.few
        (fun h0 => by rw [hheld t]; simp [hut, h0])
    unfold mPot
    exact Nat.add_le_add (Nat.mul_le_mul_right N ha) hp
  · intro hut h0 hub hu0
    have ht' : heldIn (cards.set i c') t = 0 := by rw [hheld t]; simp [hut, h0]
    have hp := pPart_lt N t (ten := l.tenants) (ten' := l.tenants) (held := heldIn cards)
      (held' := heldIn (cards.set i c')) (u := u) (List.Sublist.refl _)
      (fun w _ hw0 => by rw [hheld w] at hw0; omega) h0 ht' hub hu0
      (fun _ => by rw [hheld u]; simp)
    unfold mPot
    have := Nat.mul_le_mul_right N ha
    omega
  · intro hut hxb hx0
    subst hut
    have ha' := aPart_lt m (ms := l.models u) (ms' := l.models u) (placed := placedIn cards)
      (placed' := placedIn (cards.set i c')) (x := x) (List.Sublist.refl _) (fun y _ => hplaced y) hxb hx0
      (fun _ => hxp)
    have hN : 1 ≤ N := by
      have := List.length_pos_of_mem hw.tenant
      have := hw.few
      omega
    have hp' : pPart N u l.tenants (heldIn (cards.set i c')) = N - 1 := by
      have : heldIn (cards.set i c') u ≠ 0 := by rw [hheld u]; simp
      simp [pPart, this]
    unfold mPot
    rw [hp']
    have h1 := Nat.mul_le_mul_right N ha'
    have h2 : (aPart m (l.models u) (placedIn (cards.set i c')) + 1) * N =
        aPart m (l.models u) (placedIn (cards.set i c')) * N + N := by ring
    omega

/-- **A turn changes hands** on card `i`, to a tenant other than `t`, the
model staying: the flow still waits, and the measure is no higher. It is
lower if `t` holds no card and the turn goes to somebody before it in the
line who holds none either. -/
theorem mpot_pass {cards : List (Card T M C)} {l : Lines T M} {i : Nat} {c c' : Card T M C} {u : T}
    (hw : MWaiting N t m cards l) (hi : cards[i]? = some c) (hs : c.taken = true)
    (hs' : c'.taken = true) (ho : c'.owner = some u) (hhas : ∀ y, c'.has y = c.has y) (hut : u ≠ t)
    (huo : some u ≠ c.owner) :
    MWaiting N t m (cards.set i c') (l.tenantToBack c.owner) ∧
      mPot N t m (cards.set i c') (l.tenantToBack c.owner) ≤ mPot N t m cards l ∧
      (heldIn cards t = 0 → u ∈ before l.tenants t → heldIn cards u = 0 →
        mPot N t m (cards.set i c') (l.tenantToBack c.owner) + 1 ≤ mPot N t m cards l) := by
  have hcmem : c ∈ cards := List.mem_of_getElem? hi
  have hheld : ∀ v, heldIn (cards.set i c') v + (if c.owner = some v then 1 else 0) =
      heldIn cards v + (if u = v then 1 else 0) := by
    intro v
    have := heldIn_set c' v hi
    simpa [hs, hs', ho] using this
  have hplaced : placedIn (cards.set i c') = placedIn cards := by
    funext y
    exact any_set_congr _ cards i c c' hi (hhas y)
  have hten : t ∈ (l.tenantToBack c.owner).tenants := by
    cases hown : c.owner with
    | none => simpa using hw.tenant
    | some v => simpa using hw.tenant
  have hfew : (l.tenantToBack c.owner).tenants.length ≤ N := by
    cases hown : c.owner with
    | none => simpa using hw.few
    | some v => simpa [(toBack_perm l.tenants v).length_eq] using hw.few
  have ha : aPart m ((l.tenantToBack c.owner).models t) (placedIn (cards.set i c')) =
      aPart m (l.models t) (placedIn cards) := by rw [hplaced]; simp
  -- nobody new stands before `t`, and nobody before `t` is newly without a card
  have hsub : (before (l.tenantToBack c.owner).tenants t).Sublist (before l.tenants t) ∨ c.owner = some t := by
    cases hown : c.owner with
    | none => left; simp
    | some v =>
      by_cases hvt : v = t
      · right; rw [hvt]
      · left
        simp only [tenantToBack_tenants]
        rw [before_toBack hw.nodup.1 hw.tenant hvt]
        exact List.filter_sublist
  have hzero : c.owner ≠ some t → ∀ w ∈ before (l.tenantToBack c.owner).tenants t,
      heldIn (cards.set i c') w = 0 → heldIn cards w = 0 := by
    intro hot w hw1 hw0
    have h1 := hheld w
    cases hown : c.owner with
    | none =>
      simp only [hown, reduceCtorEq, ite_false] at h1
      omega
    | some v =>
      have hvt : v ≠ t := fun h => hot (by rw [hown, h])
      rw [hown] at hw1
      simp only [tenantToBack_tenants] at hw1
      rw [before_toBack hw.nodup.1 hw.tenant hvt, List.mem_filter] at hw1
      have hwv : w ≠ v := by simpa using hw1.2
      have hne : ¬ (c.owner = some w) := by rw [hown]; exact fun h => hwv (Option.some.inj h).symm
      simp only [hne, ite_false] at h1
      omega
  refine ⟨⟨tenantToBack_nodup _ hw.nodup, hten, by simpa using hw.model, hfew, ?_⟩, ?_, ?_⟩
  · intro d hd
    rcases List.mem_or_eq_of_mem_set hd with h1 | h1
    · exact hw.away d h1
    · rw [h1, hhas]
      exact hw.away c hcmem
  · have hp : pPart N t (l.tenantToBack c.owner).tenants (heldIn (cards.set i c')) ≤
        pPart N t l.tenants (heldIn cards) := by
      by_cases h0 : heldIn cards t = 0
      · have hot : c.owner ≠ some t := by
          intro h
          have := heldIn_pos hcmem hs h
          omega
        rcases hsub with hsub | hsub
        · refine pPart_le N t hsub (hzero hot) hten hfew fun _ => ?_
          have := hheld t
          simp only [hot, hut, ite_false] at this
          omega
        · exact absurd hsub hot
      · have := pPart_le_max N t (heldIn (cards.set i c')) hten hfew
        simp only [pPart, h0, ite_false] at this ⊢
        exact this
    unfold mPot
    rw [ha]
    omega
  · intro h0 hub hu0
    have hot : c.owner ≠ some t := by
      intro h
      have := heldIn_pos hcmem hs h
      omega
    have ht' : heldIn (cards.set i c') t = 0 := by
      have := hheld t
      simp only [hot, hut, ite_false] at this
      omega
    have hu' : heldIn (cards.set i c') u ≠ 0 := by
      have := hheld u
      have hne : c.owner ≠ some u := fun h => huo h.symm
      simp only [hne, ite_false, ite_true] at this
      omega
    rcases hsub with hsub | hsub
    · have hp := pPart_lt N t hsub (hzero hot) h0 ht' hub hu0 fun _ => hu'
      unfold mPot
      rw [ha]
      omega
    · exact absurd hsub hot

end multi

end Timeshare
