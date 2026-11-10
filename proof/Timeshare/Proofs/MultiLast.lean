/-
The turn that takes a tenant's last card lowers the measure: `rule_last`.
Whoever takes it held no card (it ranked below the owner, who held one)
and stands before the old owner now, who has gone to the back.
-/
import Timeshare.Proofs.MultiTimed

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

section multi
variable (N : Nat) (t : T) (m : M)

/-- `t`'s only card passes to `u`: `t` holds none now and is last in line,
and `u`, who holds a card, is one fewer to wait for. -/
theorem mpot_pass_last {cards : List (Card T M C)} {l : Lines T M} {i : Nat} {c c' : Card T M C} {u : T}
    (hw : MWaiting N t m cards l) (hi : cards[i]? = some c) (hs : c.taken = true)
    (hs' : c'.taken = true) (ho : c'.owner = some u) (hhas : ∀ y, c'.has y = c.has y) (hut : u ≠ t)
    (hot : c.owner = some t) (h1 : heldIn cards t = 1) (hul : u ∈ l.tenants) :
    mPot N t m (cards.set i c') (l.tenantToBack c.owner) + 1 ≤ mPot N t m cards l := by
  have hheld : ∀ v, heldIn (cards.set i c') v + (if c.owner = some v then 1 else 0) =
      heldIn cards v + (if u = v then 1 else 0) := by
    intro v
    have := heldIn_set c' v hi
    simpa [hs, hs', ho] using this
  have hplaced : placedIn (cards.set i c') = placedIn cards := by
    funext y
    exact any_set_congr _ cards i c c' hi (hhas y)
  have ha : aPart m ((l.tenantToBack c.owner).models t) (placedIn (cards.set i c')) =
      aPart m (l.models t) (placedIn cards) := by rw [hplaced]; simp
  have ht' : heldIn (cards.set i c') t = 0 := by
    have := hheld t
    simp only [hot, hut, ite_true, ite_false] at this
    omega
  have hu' : heldIn (cards.set i c') u ≠ 0 := by
    have := hheld u
    have hne : ¬ (c.owner = some u) := by rw [hot]; exact fun h => hut (Option.some.inj h).symm
    simp only [hne, ite_false, ite_true] at this
    omega
  have hp : pPart N t (l.tenantToBack c.owner).tenants (heldIn (cards.set i c')) + 1 ≤
      pPart N t l.tenants (heldIn cards) := by
    have hbefore : pPart N t l.tenants (heldIn cards) = N - 1 := by simp [pPart, h1]
    rw [hbefore, hot]
    simp only [pPart, ht', ite_true, tenantToBack_tenants, before_toBack_self hw.nodup.1 hw.tenant]
    have hmem : u ∈ l.tenants.erase t := (List.Nodup.mem_erase_iff hw.nodup.1).mpr ⟨hut, hul⟩
    have hlt : ((l.tenants.erase t).filter fun w => Decidable.decide (heldIn (cards.set i c') w = 0)).length <
        (l.tenants.erase t).length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨u, hmem, by simpa using hu'⟩
    have hlen : (l.tenants.erase t).length = l.tenants.length - 1 := List.length_erase_of_mem hw.tenant
    have := hw.few
    omega
  unfold mPot
  rw [ha]
  omega

omit [DecidableEq M] in
/-- If `t` holds no card once card `i` has changed, it held at most that one. -/
theorem held_before {cards : List (Card T M C)} {i : Nat} {c : Card T M C} (c' : Card T M C)
    (hi : cards[i]? = some c) (hz : heldIn (cards.set i c') t = 0) :
    heldIn cards t + (if (c'.taken && Decidable.decide (c'.owner = some t)) = true then 1 else 0) =
      (if (c.taken && Decidable.decide (c.owner = some t)) = true then 1 else 0) := by
  have := heldIn_set c' t hi
  omega

/-- **The turn that takes `t`'s last card** lowers the measure. -/
theorem rule_last {w w' : World T M C} {a : Action T M C} (hw : MWaiting N t m w.cards w.lines)
    (h : w.rule = some (a, w')) (hno : Spares m a) (hbeg : begins w a = true)
    (h0 : heldIn w.cards t ≠ 0) (h0' : heldIn w'.cards t = 0) :
    mPot N t m w'.cards w'.lines + 1 ≤ mPot N t m w.cards w.lines := by
  have hlostm : w.placed m = false := not_placed_of_away m hw.away
  have hlost : (w.lost t).isSome = true := by
    unfold World.lost
    rw [List.find?_isSome]
    exact ⟨m, hw.model, by simp [hlostm]⟩
  cases rule_effect h with
  | drained i d hd hst _ => simp [begins] at hbeg
  | reserved i d hd hst hnext =>
    have hpend : w.pending = true := by
      unfold World.pending
      rw [List.any_eq_true]
      exact ⟨d, List.mem_of_getElem? hd, by simp [hst, hnext]⟩
    simp [begins, hpend] at hbeg
  | start i d u x hd hst hnext _ _ =>
    -- a start gives a card, it takes none
    have := heldIn_set ({ id := d.id, st := .starting, model := some x, owner := some u, since := w.now } :
      Card T M C) t hd
    simp only [Card.taken, Card.serving, hst, hnext, reduceCtorEq, decide_false, Bool.or_self, Option.isSome_none,
      Bool.false_and, Bool.false_eq_true, ite_false] at this
    have h0'' : heldIn (w.cards.set i
      ({ id := d.id, st := .starting, model := some x, owner := some u, since := w.now } : Card T M C)) t = 0 := h0'
    omega
  | stop i d dur hd hidle => simp [begins] at hbeg
  | pass i d u mu hd hwin hown hmod =>
    have hup := (winner_old hwin).1
    have hs : d.serving = true := by simp [Card.serving, hup]
    have hdt : d.taken = true := by simp [Card.taken, hs]
    have hdmem : d ∈ w.cards := List.mem_of_getElem? hd
    have hut : u ≠ t := by
      rintro rfl
      obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hlost
      have hmm := winner_lost hwin hm'
      subst hmm
      have h1 := lost_not_placed hm'
      have h2 : w.placed mu = true := by
        unfold World.placed
        rw [List.any_eq_true]
        exact ⟨d, hdmem, by simp [Card.has, hs, hmod.symm]⟩
      rw [h1] at h2
      cases h2
    have hheld := held_before t ({ d with owner := some u, turnAt := w.now } : Card T M C) hd h0'
    have hne : ¬ (some u = some t) := fun h1 => hut (Option.some.inj h1)
    simp only [hne, decide_false, Bool.and_false, Bool.false_eq_true, ite_false, Nat.add_zero, hdt,
      Bool.true_and, decide_eq_true_eq] at hheld
    have hot : d.owner = some t := by
      by_contra hc
      simp only [hc, ite_false] at hheld
      omega
    have h1 : heldIn w.cards t = 1 := by
      simp only [hot, ite_true] at hheld
      exact hheld
    exact mpot_pass_last N t m (c' := { d with owner := some u, turnAt := w.now }) hw hd hdt
      (by simp [Card.taken, Card.serving, hup]) rfl (by intro y; simp [Card.has, Card.serving, hup]) hut hot h1
      (winner_mem hwin)
  | drain i d u mu hd hwin hne =>
    have hup := (winner_old hwin).1
    have hs : d.serving = true := by simp [Card.serving, hup]
    have hdt : d.taken = true := by simp [Card.taken, hs]
    have hdmem : d ∈ w.cards := List.mem_of_getElem? hd
    have hmum : mu ≠ m := fun hx => hno.2 rfl (by rw [hx])
    have hlt : i < w.cards.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hd
      cases hd
    -- who held what: `t` held one card, this one, and `u` is not `t`
    show mPot N t m (w.cards.set i
      ({ d with st := .draining, owner := some u, next := some mu, since := w.now } : Card T M C))
      (w.lines.ended d.owner d.model) + 1 ≤ mPot N t m w.cards w.lines
    have hheld := held_before t
      ({ d with st := .draining, owner := some u, next := some mu, since := w.now } : Card T M C) hd h0'
    have hct : ({ d with st := .draining, owner := some u, next := some mu, since := w.now } :
        Card T M C).taken = true := by simp [Card.taken]
    rw [hct, hdt] at hheld
    simp only [Bool.true_and, decide_eq_true_eq, Option.some.injEq] at hheld

    have hut : u ≠ t := by
      intro hc
      simp only [hc, ite_true] at hheld
      split at hheld <;> omega
    have hot : d.owner = some t := by
      by_contra hc
      simp only [hc, hut, ite_false] at hheld
      omega
    have h1 : heldIn w.cards t = 1 := by
      simp only [hot, hut, ite_true, ite_false] at hheld
      omega

    -- `u` ranks no higher than `t`, the owner with one card: it holds none
    have hu0 : w.held u = 0 := by
      have hle := winner_le hwin hw.tenant hlost
      have huo : ¬ (some u = d.owner) := by rw [hot]; exact fun h2 => hut (Option.some.inj h2)
      have hto : some t = d.owner := hot.symm
      simp only [World.rank, huo, hto, ite_false, ite_true] at hle
      rw [held_eq w t, h1] at hle
      omega
    obtain ⟨hw1, hle1⟩ := mpot_ended N t m { id := d.id } hw hd hs (by simp [Card.taken, Card.serving])
    have hi1 : (w.cards.set i { id := d.id })[i]? = some ({ id := d.id } : Card T M C) := by simp [hlt]
    obtain ⟨_, _, hB, _⟩ := mpot_start N t m (u := u) (x := mu)
      (c' := { d with st := .draining, owner := some u, next := some mu, since := w.now }) hw1 hi1
      (by simp [Card.taken, Card.serving]) (by simp [Card.taken]) rfl
      (by simp [Card.has, Card.serving]) (by simp [Card.has, Card.serving, hmum])
    rw [List.set_set] at hB
    have hheld1 : ∀ v, heldIn (w.cards.set i { id := d.id }) v ≤ heldIn w.cards v := by
      intro v
      have := heldIn_set ({ id := d.id } : Card T M C) v hd
      simp only [Card.taken, Card.serving, reduceCtorEq, decide_false, Bool.or_self, Option.isSome_none,
        Bool.false_and, Bool.false_eq_true, ite_false] at this
      omega
    have h01 : heldIn (w.cards.set i { id := d.id }) t = 0 := by
      have := heldIn_set ({ id := d.id } : Card T M C) t hd
      simp only [Card.taken, Card.serving, hup, hot, reduceCtorEq, decide_true, decide_false, Bool.or_self,
        Bool.or_true, Bool.true_or, Option.isSome_none, Bool.false_and, Bool.true_and, Bool.false_eq_true,
        ite_false, ite_true] at this
      omega
    have hu01 : heldIn (w.cards.set i { id := d.id }) u = 0 := by
      have := hheld1 u
      rw [← held_eq] at this
      omega
    have hub1 : u ∈ before (w.lines.ended d.owner d.model).tenants t := by
      rw [hot]
      simp only [ended_tenants, tenantToBack_tenants, before_toBack_self hw.nodup.1 hw.tenant]
      exact (List.Nodup.mem_erase_iff hw.nodup.1).mpr ⟨hut, winner_mem hwin⟩
    have := hB hut h01 hub1 hu01
    omega

end multi

assert_no_sorry rule_last

end Timeshare
