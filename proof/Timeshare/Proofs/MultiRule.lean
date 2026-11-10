/-
Any number of cards: every rule, and everything a model server does,
leaves the measure of Multi.lean no higher; a turn that begins while the
waiting flow's tenant holds no card, and every turn of that tenant's own,
lowers it. So (`mturns_bound`): while a flow (tenant `t`, model `m`)
waits, at most `K * N - 1` turns begin that are `t`'s own or begin while
`t` holds no card.
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

/-- A card changes in a way the measure does not see (requests come and
go, a load finishes, a drained card stops): nothing changes. -/
theorem mpot_congr {cards : List (Card T M C)} {l : Lines T M} {i : Nat} {c : Card T M C} (c' : Card T M C)
    (hw : MWaiting N t m cards l) (hi : cards[i]? = some c) (hs : c'.serving = c.serving)
    (hsame : c.serving = true → c'.owner = c.owner ∧ c'.model = c.model) :
    MWaiting N t m (cards.set i c') l ∧ mPot N t m (cards.set i c') l = mPot N t m cards l := by
  have hheld : ∀ v, heldIn (cards.set i c') v = heldIn cards v := by
    intro v
    have := heldIn_set c' v hi
    by_cases h : c.serving = true
    · rw [hs, (hsame h).1] at this
      omega
    · have h' : c.serving = false := by simpa using h
      simp only [hs, h', Bool.false_and, Bool.false_eq_true, ite_false] at this
      omega
  have hplaced : ∀ y, placedIn (cards.set i c') y = placedIn cards y := by
    intro y
    refine any_set_congr _ cards i c c' hi ?_
    by_cases h : c.serving = true
    · rw [hs, (hsame h).2]
    · have h' : c.serving = false := by simpa using h
      simp [hs, h']
  refine ⟨⟨hw.nodup, hw.tenant, hw.model, hw.few, ?_⟩, ?_⟩
  · intro d hd hds
    rcases List.mem_or_eq_of_mem_set hd with h1 | h1
    · exact hw.away d h1 hds
    · subst h1
      have hcs : c.serving = true := by rw [← hs]; exact hds
      rw [(hsame hcs).2]
      exact hw.away c (List.mem_of_getElem? hi) hcs
  · unfold mPot
    rw [show heldIn (cards.set i c') = heldIn cards from funext hheld,
      show placedIn (cards.set i c') = placedIn cards from funext hplaced]

/-- What a start on a free card does to the cards the measure counts. -/
theorem start_facts {cards : List (Card T M C)} {i : Nat} {c c' : Card T M C} {u : T} {x : M}
    (hi : cards[i]? = some c) (hs : c.serving = false) (hs' : c'.serving = true) (ho : c'.owner = some u)
    (hmod : c'.model = some x) :
    (∀ v, heldIn (cards.set i c') v = heldIn cards v + (if u = v then 1 else 0)) ∧
    (∀ y, placedIn (cards.set i c') y = false → placedIn cards y = false) ∧
    placedIn (cards.set i c') x = true := by
  refine ⟨fun v => ?_, fun y hp => ?_, ?_⟩
  · have := heldIn_set c' v hi
    simp only [hs, hs', ho, Bool.false_and, Bool.true_and, Bool.false_eq_true, ite_false,
      decide_eq_true_eq, Option.some.injEq] at this
    omega
  · by_contra hpl
    have hpl' : placedIn cards y = true := by simpa using hpl
    have : placedIn (cards.set i c') y = true := any_of_set _ cards i c c' hi (by simp [hs]) hpl'
    rw [hp] at this
    cases this
  · unfold placedIn
    rw [List.any_eq_true]
    refine ⟨c', ?_, by simp [hs', hmod]⟩
    have hlt : i < cards.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hi
      cases hi
    exact List.mem_iff_getElem?.mpr ⟨i, by simp [hlt]⟩

/-- **A turn starts** on a free card, not `m`: the flow still waits. If it
is `t`'s own turn, or `t` holds no card and the turn goes to somebody
before it in the line who holds none either, the measure is lower; if `t`
holds a card, it is no higher. -/
theorem mpot_start {cards : List (Card T M C)} {l : Lines T M} {i : Nat} {c c' : Card T M C} {u : T} {x : M}
    (hw : MWaiting N t m cards l) (hi : cards[i]? = some c) (hs : c.serving = false)
    (hs' : c'.serving = true) (ho : c'.owner = some u) (hmod : c'.model = some x) (hxm : x ≠ m) :
    MWaiting N t m (cards.set i c') l ∧
      (u ≠ t → heldIn cards t ≠ 0 → mPot N t m (cards.set i c') l ≤ mPot N t m cards l) ∧
      (u ≠ t → heldIn cards t = 0 → u ∈ before l.tenants t → heldIn cards u = 0 →
        mPot N t m (cards.set i c') l + 1 ≤ mPot N t m cards l) ∧
      (u = t → x ∈ before (l.models t) m → placedIn cards x = false →
        mPot N t m (cards.set i c') l + 1 ≤ mPot N t m cards l) := by
  obtain ⟨hheld, hplaced, hx⟩ := start_facts hi hs hs' ho hmod
  have ha : aPart m (l.models t) (placedIn (cards.set i c')) ≤ aPart m (l.models t) (placedIn cards) :=
    aPart_le m (List.Sublist.refl _) fun y _ => hplaced y
  refine ⟨⟨hw.nodup, hw.tenant, hw.model, hw.few, ?_⟩, ?_, ?_, ?_⟩
  · intro d hd hds
    rcases List.mem_or_eq_of_mem_set hd with h1 | h1
    · exact hw.away d h1 hds
    · subst h1
      rw [hmod]
      exact fun h => hxm (Option.some.inj h)
  · intro hut h0
    have ht' : heldIn (cards.set i c') t = heldIn cards t := by rw [hheld t]; simp [hut]
    unfold mPot
    have hp : pPart N t l.tenants (heldIn (cards.set i c')) = pPart N t l.tenants (heldIn cards) := by
      simp [pPart, ht', h0]
    rw [hp]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right N ha) _
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
      (fun _ => hx)
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

/-- **A turn changes hands** on card `i`, to a tenant other than `t`: the
flow still waits. If `t` holds no card and the turn goes to somebody before
it in the line who holds none either, the measure is lower; if `t` holds a
card, it is no higher. -/
theorem mpot_pass {cards : List (Card T M C)} {l : Lines T M} {i : Nat} {c c' : Card T M C} {u : T}
    (hw : MWaiting N t m cards l) (hi : cards[i]? = some c) (hs : c.serving = true)
    (hs' : c'.serving = true) (ho : c'.owner = some u) (hmod : c'.model = c.model) (hut : u ≠ t)
    (huo : some u ≠ c.owner) :
    MWaiting N t m (cards.set i c') (l.tenantToBack c.owner) ∧
      (heldIn cards t ≠ 0 →
        mPot N t m (cards.set i c') (l.tenantToBack c.owner) ≤ mPot N t m cards l) ∧
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
    exact any_set_congr _ cards i c c' hi (by simp [hs, hs', hmod])
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
  refine ⟨⟨tenantToBack_nodup _ hw.nodup, hten, by simpa using hw.model, hfew, ?_⟩, ?_, ?_⟩
  · intro d hd hds
    rcases List.mem_or_eq_of_mem_set hd with h1 | h1
    · exact hw.away d h1 hds
    · subst h1
      rw [hmod]
      exact hw.away c hcmem hs
  · intro h0
    have := pPart_le_max N t (heldIn (cards.set i c')) hten hfew
    unfold mPot
    rw [ha]
    have hp : pPart N t l.tenants (heldIn cards) = N - 1 := by simp [pPart, h0]
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
    have hp : pPart N t (l.tenantToBack c.owner).tenants (heldIn (cards.set i c')) + 1 ≤
        pPart N t l.tenants (heldIn cards) := by
      cases hown : c.owner with
      | none =>
        refine pPart_lt N t (by simp) (fun w _ hw0 => ?_) h0 ht' hub hu0 fun _ => hu'
        have := hheld w
        simp only [hown, reduceCtorEq, ite_false] at this
        omega
      | some v =>
        have hvt : v ≠ t := fun h => hot (by rw [hown, h])
        have hb := before_toBack hw.nodup.1 hw.tenant hvt
        refine pPart_lt N t (by simp only [tenantToBack_tenants]; rw [hb]; exact List.filter_sublist)
          (fun w hw1 hw0 => ?_) h0 ht' hub hu0 fun _ => hu'
        simp only [tenantToBack_tenants] at hw1
        rw [hb, List.mem_filter] at hw1
        have hwv : w ≠ v := by simpa using hw1.2
        have := hheld w
        have hne : ¬ (c.owner = some w) := by rw [hown]; exact fun h => hwv (Option.some.inj h).symm
        simp only [hne, ite_false] at this
        omega
    unfold mPot
    rw [ha]
    omega

end multi

end Timeshare
