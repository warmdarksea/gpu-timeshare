/-
Any number of cards: what can be said of a flow that waits, whatever the
cards are doing.

The measure (`mPot`) is the one of one card (Potential.lean) with the
cards counted in. For a flow (tenant `t`, model `m`):

- `aPart`: `t`'s models that stand before `m` in its line and are on no
  card. Each of `t`'s own turns starts one of them, or `m`.
- `pPart`: while `t` holds no card, the tenants that stand before `t` in
  the line and hold no card either. Each turn that begins then goes to one
  of them, or to `t`. While `t` holds a card, the most it can be when `t`
  holds none again.

No step raises it. A turn that begins while `t` holds no card lowers it,
and so does every turn of `t`'s own (`rule_multi`, `mturns_bound`).
-/
import Timeshare.Proofs.Progress

namespace Timeshare

/-! ### Lists -/

section lists
variable {α : Type}

theorem length_filter_set (P : α → Bool) : ∀ (l : List α) (i : Nat) (c c' : α), l[i]? = some c →
    ((l.set i c').filter P).length + (if P c = true then 1 else 0) =
      (l.filter P).length + (if P c' = true then 1 else 0) := by
  intro l
  induction l with
  | nil => intro i c c' h; simp at h
  | cons z zs ih =>
    intro i c c' h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.filter_cons]
      by_cases h1 : P z = true <;> by_cases h2 : P c' = true <;> simp [h1, h2]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have := ih i c c' h
      simp only [List.set_cons_succ, List.filter_cons]
      by_cases h1 : P z = true <;> simp [h1] <;> omega

theorem any_of_set (P : α → Bool) : ∀ (l : List α) (i : Nat) (c c' : α), l[i]? = some c → P c = false →
    l.any P = true → (l.set i c').any P = true := by
  intro l
  induction l with
  | nil => intro i c c' h; simp at h
  | cons z zs ih =>
    intro i c c' h hc hany
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.any_cons, hc, Bool.false_or] at hany
      simp [hany]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.any_cons, Bool.or_eq_true] at hany
      simp only [List.set_cons_succ, List.any_cons, Bool.or_eq_true]
      rcases hany with h1 | h1
      · left; exact h1
      · right; exact ih i c c' h hc h1

theorem length_filter_le_of_imp {p q : α → Bool} : ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
    (l.filter p).length ≤ (l.filter q).length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons z zs ih =>
    intro h
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hz := h z (List.mem_cons_self ..)
    simp only [List.filter_cons]
    by_cases h1 : p z = true
    · simp [h1, hz h1]; exact ih'
    · by_cases h2 : q z = true
      · simp [h1, h2]; omega
      · simp [h1, h2]; exact ih'

end lists

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

/-! ### The measure, on what it depends on -/

section parts
variable (N : Nat) (t : T) (m : M)

/-- While `t` holds no card: the tenants before it in the line that hold
none either. While it holds one: `N - 1`. -/
def pPart (ten : List T) (held : T → Nat) : Nat :=
  if held t = 0 then ((before ten t).filter fun u => held u = 0).length else N - 1

/-- `t`'s models before `m` in its line that are on no card. -/
def aPart (ms : List M) (placed : M → Bool) : Nat :=
  ((before ms m).filter fun y => !placed y).length

theorem pPart_le_max {ten : List T} (held : T → Nat) (ht : t ∈ ten) (hN : ten.length ≤ N) :
    pPart N t ten held ≤ N - 1 := by
  unfold pPart
  split
  · have h1 := List.length_filter_le (fun u => Decidable.decide (held u = 0)) (before ten t)
    have h2 := before_length_lt ht
    omega
  · exact le_rfl

/-- Nobody new before `t`, and nobody before `t` newly without a card:
`pPart` is no higher. -/
theorem pPart_le {ten ten' : List T} {held held' : T → Nat}
    (hsub : (before ten' t).Sublist (before ten t))
    (h1 : ∀ w ∈ before ten' t, held' w = 0 → held w = 0)
    (ht' : t ∈ ten') (hN' : ten'.length ≤ N) (h2 : held t = 0 → held' t = 0) :
    pPart N t ten' held' ≤ pPart N t ten held := by
  by_cases h0 : held t = 0
  · have h0' := h2 h0
    simp only [pPart, h0, h0', ite_true]
    refine le_trans (length_filter_le_of_imp _ fun w hw hw0 => ?_) (hsub.filter _).length_le
    simpa using h1 w hw (by simpa using hw0)
  · have := pPart_le_max N t held' ht' hN'
    simp only [pPart, h0, ite_false] at this ⊢
    exact this

/-- ... and one lower, if somebody who was before `t` without a card is
no longer. -/
theorem pPart_lt {ten ten' : List T} {held held' : T → Nat} {u : T}
    (hsub : (before ten' t).Sublist (before ten t))
    (h1 : ∀ w ∈ before ten' t, held' w = 0 → held w = 0)
    (h0 : held t = 0) (h0' : held' t = 0) (hu : u ∈ before ten t) (hu0 : held u = 0)
    (hgone : u ∈ before ten' t → held' u ≠ 0) :
    pPart N t ten' held' + 1 ≤ pPart N t ten held := by
  simp only [pPart, h0, h0', ite_true]
  have hmem : u ∈ (before ten t).filter fun w => Decidable.decide (held w = 0) :=
    List.mem_filter.mpr ⟨hu, by simpa using hu0⟩
  have hlt := length_filter_ne_lt hmem
  refine le_trans (Nat.add_le_add_right ?_ 1) hlt
  rw [List.filter_filter]
  refine le_trans (length_filter_le_of_imp (q := fun w => Decidable.decide (w ≠ u) && Decidable.decide (held w = 0)) _
    fun w hw hw0 => ?_) (hsub.filter _).length_le
  have hw0' : held' w = 0 := by simpa using hw0
  have hne : w ≠ u := by
    rintro rfl
    exact hgone hw hw0'
  simp [hne, h1 w hw hw0']

omit [DecidableEq T] in
theorem aPart_le {ms ms' : List M} {placed placed' : M → Bool}
    (hsub : (before ms' m).Sublist (before ms m))
    (h1 : ∀ y ∈ before ms' m, placed' y = false → placed y = false) :
    aPart m ms' placed' ≤ aPart m ms placed := by
  unfold aPart
  refine le_trans (length_filter_le_of_imp _ fun y hy hp => ?_) (hsub.filter _).length_le
  simpa using h1 y hy (by simpa using hp)

omit [DecidableEq T] in
theorem aPart_lt {ms ms' : List M} {placed placed' : M → Bool} {x : M}
    (hsub : (before ms' m).Sublist (before ms m))
    (h1 : ∀ y ∈ before ms' m, placed' y = false → placed y = false)
    (hx : x ∈ before ms m) (hx0 : placed x = false) (hgone : x ∈ before ms' m → placed' x = true) :
    aPart m ms' placed' + 1 ≤ aPart m ms placed := by
  unfold aPart
  have hmem : x ∈ (before ms m).filter fun y => !placed y := List.mem_filter.mpr ⟨hx, by simp [hx0]⟩
  have hlt := length_filter_ne_lt hmem
  refine le_trans (Nat.add_le_add_right ?_ 1) hlt
  rw [List.filter_filter]
  refine le_trans (length_filter_le_of_imp (q := fun y => Decidable.decide (y ≠ x) && !placed y) _
    fun y hy hp => ?_) (hsub.filter _).length_le
  have hp' : placed' y = false := by simpa using hp
  have hne : y ≠ x := by
    rintro rfl
    rw [hgone hy] at hp'
    cases hp'
  simp [hne, h1 y hy hp']

end parts

/-! ### The cards -/

omit [DecidableEq M] in
/-- How many cards have a turn of `u`'s (`World.held`, of the cards alone). -/
def heldIn (cards : List (Card T M C)) (u : T) : Nat :=
  (cards.filter fun c => c.serving && c.owner = some u).length

omit [DecidableEq T] in
/-- `y` is on a card (`World.placed`, of the cards alone). -/
def placedIn (cards : List (Card T M C)) (y : M) : Bool :=
  cards.any fun c => c.serving && c.model = some y

omit [DecidableEq M] in
theorem held_eq (w : World T M C) (u : T) : w.held u = heldIn w.cards u := rfl

omit [DecidableEq T] in
theorem placed_eq (w : World T M C) (y : M) : w.placed y = placedIn w.cards y := rfl

omit [DecidableEq M] in
theorem heldIn_set {cards : List (Card T M C)} {i : Nat} {c : Card T M C} (c' : Card T M C) (u : T)
    (hi : cards[i]? = some c) :
    heldIn (cards.set i c') u + (if (c.serving && Decidable.decide (c.owner = some u)) = true then 1 else 0) =
      heldIn cards u + (if (c'.serving && Decidable.decide (c'.owner = some u)) = true then 1 else 0) :=
  length_filter_set _ cards i c c' hi

omit [DecidableEq M] in
theorem heldIn_pos {cards : List (Card T M C)} {c : Card T M C} {u : T} (hc : c ∈ cards)
    (hs : c.serving = true) (ho : c.owner = some u) : 0 < heldIn cards u := by
  unfold heldIn
  apply List.length_pos_of_mem (a := c)
  exact List.mem_filter.mpr ⟨hc, by simp [hs, ho]⟩

theorem find?_before {α : Type} [DecidableEq α] {p : α → Bool} : ∀ {l : List α} {x y : α},
    l.find? p = some x → y ∈ l → p y = true → x = y ∨ x ∈ before l y := by
  intro l
  induction l with
  | nil => intro x y h; simp at h
  | cons z zs ih =>
    intro x y h hy hpy
    by_cases hpz : p z = true
    · rw [List.find?_cons_of_pos (h := hpz)] at h
      cases h
      by_cases hzy : z = y
      · left; exact hzy
      · right; exact head_mem_before hzy
    · rw [List.find?_cons_of_neg (h := hpz)] at h
      have hzy : z ≠ y := fun hzy => hpz (hzy ▸ hpy)
      have hy' : y ∈ zs := by
        rcases List.mem_cons.mp hy with h1 | h1
        · exact absurd h1.symm hzy
        · exact h1
      rcases ih h hy' hpy with h1 | h1
      · left; exact h1
      · right
        have : before (z :: zs) y = z :: before zs y := by simp [before, hzy]
        rw [this]
        exact List.mem_cons_of_mem _ h1

section multi
variable (N : Nat) (t : T) (m : M)

/-- What stays true while the flow (`t`, `m`) waits, whatever the cards. -/
structure MWaiting (cards : List (Card T M C)) (l : Lines T M) : Prop where
  nodup : l.Nodup
  tenant : t ∈ l.tenants
  model : m ∈ l.models t
  few : l.tenants.length ≤ N
  /-- no card has `m` -/
  away : ∀ c ∈ cards, c.serving = true → c.model ≠ some m

/-- The measure, for any number of cards. -/
def mPot (cards : List (Card T M C)) (l : Lines T M) : Nat :=
  aPart m (l.models t) (placedIn cards) * N + pPart N t l.tenants (heldIn cards)

omit [DecidableEq T] in
theorem not_placed_of_away {cards : List (Card T M C)}
    (h : ∀ c ∈ cards, c.serving = true → c.model ≠ some m) : placedIn cards m = false := by
  unfold placedIn
  rw [List.any_eq_false]
  intro c hc
  by_cases hs : c.serving = true
  · simp [hs, h c hc hs]
  · simp [hs]

/-- **A turn ends** on card `i` (a drain, an idle stop, a failure): the
flow still waits, and the measure is no higher. -/
theorem mpot_ended {cards : List (Card T M C)} {l : Lines T M} {i : Nat} {c : Card T M C} (c' : Card T M C)
    (hw : MWaiting N t m cards l) (hi : cards[i]? = some c) (hs : c.serving = true)
    (hs' : c'.serving = false) :
    MWaiting N t m (cards.set i c') (l.ended c.owner c.model) ∧
      mPot N t m (cards.set i c') (l.ended c.owner c.model) ≤ mPot N t m cards l := by
  have hcmem : c ∈ cards := List.mem_of_getElem? hi
  have hxm : c.model ≠ some m := hw.away c hcmem hs
  have hten : t ∈ (l.ended c.owner c.model).tenants := by
    cases ho : c.owner with
    | none => simpa using hw.tenant
    | some v => simpa using hw.tenant
  have hfew : (l.ended c.owner c.model).tenants.length ≤ N := by
    cases ho : c.owner with
    | none => simpa using hw.few
    | some v => simpa [(toBack_perm l.tenants v).length_eq] using hw.few
  have hw' : MWaiting N t m (cards.set i c') (l.ended c.owner c.model) :=
    { nodup := ended_nodup _ _ hw.nodup
      tenant := hten
      model := by
        cases hmod : c.model with
        | none => simpa using hw.model
        | some y => simpa using hw.model
      few := hfew
      away := by
        intro d hd hds
        rcases List.mem_or_eq_of_mem_set hd with h1 | h1
        · exact hw.away d h1 hds
        · rw [h1, hs'] at hds
          cases hds }
  refine ⟨hw', ?_⟩
  -- `t`'s models before `m`
  have ha : aPart m ((l.ended c.owner c.model).models t) (placedIn (cards.set i c')) ≤
      aPart m (l.models t) (placedIn cards) := by
    cases hmod : c.model with
    | none =>
      refine aPart_le m (by simp) fun y _ hp => ?_
      by_contra hpl
      have hpl' : placedIn cards y = true := by simpa using hpl
      have : placedIn (cards.set i c') y = true :=
        any_of_set _ cards i c c' hi (by simp [hmod]) hpl'
      rw [hp] at this
      cases this
    | some x =>
      have hx : x ≠ m := fun h => hxm (by rw [hmod, h])
      have hb := before_toBack (hw.nodup.2 t) hw.model hx
      refine aPart_le m (by simp only [ended_models]; rw [hb]; exact List.filter_sublist) fun y hy hp => ?_
      simp only [ended_models] at hy
      rw [hb, List.mem_filter] at hy
      have hyx : y ≠ x := by simpa using hy.2
      by_contra hpl
      have hpl' : placedIn cards y = true := by simpa using hpl
      have : placedIn (cards.set i c') y = true :=
        any_of_set _ cards i c c' hi (by simp [hmod, Ne.symm hyx]) hpl'
      rw [hp] at this
      cases this
  -- the tenants before `t`
  have hp : pPart N t (l.ended c.owner c.model).tenants (heldIn (cards.set i c')) ≤
      pPart N t l.tenants (heldIn cards) := by
    by_cases h0 : heldIn cards t = 0
    · have hot : c.owner ≠ some t := by
        intro ho
        have := heldIn_pos hcmem hs ho
        omega
      have hheld : ∀ w, c.owner ≠ some w → heldIn (cards.set i c') w = heldIn cards w := by
        intro w hne
        have := heldIn_set c' w hi
        simp only [hs, hs', hne, Bool.true_and, Bool.false_and, decide_false, Bool.false_eq_true, ite_false] at this
        omega
      cases ho : c.owner with
      | none =>
        rw [ho] at hten hfew
        refine pPart_le N t (by simp) (fun w _ hw0 => ?_) hten hfew fun h => ?_
        · rw [hheld w (by simp [ho])] at hw0; exact hw0
        · rw [hheld t hot]; exact h
      | some v =>
        have hvt : v ≠ t := fun h => hot (by rw [ho, h])
        have hb := before_toBack hw.nodup.1 hw.tenant hvt
        have hsub : (before (l.ended (some v) c.model).tenants t).Sublist (before l.tenants t) := by
          simp only [ended_tenants, tenantToBack_tenants]
          rw [hb]
          exact List.filter_sublist
        rw [ho] at hten hfew
        refine pPart_le N t hsub (fun w hw1 hw0 => ?_) hten hfew fun h => ?_
        · simp only [ended_tenants, tenantToBack_tenants] at hw1
          rw [hb, List.mem_filter] at hw1
          have hwv : w ≠ v := by simpa using hw1.2
          rw [hheld w (by rw [ho]; exact fun h => hwv (Option.some.inj h).symm)] at hw0
          exact hw0
        · rw [hheld t hot]; exact h
    · have := pPart_le_max N t (heldIn (cards.set i c')) hten hfew
      simp only [pPart, h0, ite_false] at this ⊢
      exact this
  unfold mPot
  exact Nat.add_le_add (Nat.mul_le_mul_right N ha) hp

end multi

end Timeshare
