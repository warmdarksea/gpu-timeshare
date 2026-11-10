/-
`mwait_bound`: no starvation, on any number of cards, in time. See
MultiTimed.lean for what is claimed and how; this file is the steps (one
rule, a round, what a model server does, a tick) and the theorem.
-/
import Timeshare.Proofs.MultiLast

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

section timed
variable (N : Nat) (t : T) (m : M) (pol : Policy) (L D : Nat)

/-- New lines with a measure no higher: still within the budget. -/
theorem bud_lines {C0 : Nat} {cards : List (Card T M C)} {l l' : Lines T M} {now : Nat}
    (h : Bud N t m pol L D C0 cards l now) (hpot : mPot N t m cards l' ≤ mPot N t m cards l) :
    Bud N t m pol L D C0 cards l' now := by
  have hmul := Nat.mul_le_mul_right (turn1 pol L D) hpot
  refine ⟨fun h0 c hc hp => ?_, fun h0 => ?_⟩
  · have := h.1 h0 c hc hp
    omega
  · obtain ⟨c, hc, hb⟩ := h.2 h0
    exact ⟨c, hc, by omega⟩

omit [DecidableEq M] in
theorem charged_le_one (w : World T M C) (a : Action T M C) : charged t w a ≤ 1 := by
  unfold charged
  split <;> omega

/-- **One rule** keeps the cards within the budget. -/
theorem rule_bud {C0 : Nat} {w w' : World T M C} {a : Action T M C} (hw : MWaiting N t m w.cards w.lines)
    (hb : Bud N t m pol L D C0 w.cards w.lines w.now) (h : w.rule = some (a, w')) (hno : Spares m a) :
    Bud N t m pol L D C0 w'.cards w'.lines w.now := by
  obtain ⟨_, hpot⟩ := rule_multi N t m hw h hno
  have hbase := bud_base N t m pol L D hb
  have hne' : w'.cards ≠ [] := by
    obtain ⟨i, c, c', hi, _, hset, _⟩ := rule_step h
    rw [hset]
    exact List.ne_nil_of_mem (mem_set_self c' hi)
  by_cases hch : charged t w a = 1
  · exact bud_begun N t m pol L D hbase (by omega) hne'
  have hch0 : charged t w a = 0 := by
    have := charged_le_one t w a
    omega
  have hle : mPot N t m w'.cards w'.lines ≤ mPot N t m w.cards w.lines := by omega
  by_cases hbeg : begins w a = true
  · -- a turn begins that is not charged: `t` holds a card, and the turn is not its own
    have hnz : heldIn w.cards t ≠ 0 ∧ a.tenant ≠ some t := by
      unfold charged at hch0
      rw [held_eq] at hch0
      by_contra hcon
      have : heldIn w.cards t = 0 ∨ a.tenant = some t := by
        by_contra hx
        exact hcon ⟨fun h1 => hx (Or.inl h1), fun h1 => hx (Or.inr h1)⟩
      simp [hbeg, this] at hch0
    by_cases h0' : heldIn w'.cards t = 0
    · exact bud_begun N t m pol L D hbase (rule_last N t m hw h hno hbeg hnz.1 h0') hne'
    · cases rule_effect h with
      | drained i d hd hst _ => simp [begins] at hbeg
      | reserved i d hd hst hnext =>
        have hpend : w.pending = true := by
          unfold World.pending
          rw [List.any_eq_true]
          exact ⟨d, List.mem_of_getElem? hd, by simp [hst, hnext]⟩
        simp [begins, hpend] at hbeg
      | start i d u x hd hst hnext _ _ =>
        have hut : ¬ (some u = some t) := hnz.2
        exact bud_other N t m pol L D _ hb hd hle hnz.1 h0' (by simp [hut])
      | stop i d dur hd hidle => simp [begins] at hbeg
      | pass i d u mu hd hwin _ _ =>
        have hut : ¬ (some u = some t) := hnz.2
        exact bud_other N t m pol L D _ hb hd hle hnz.1 h0' (by simp [hut])
      | drain i d u mu hd hwin _ =>
        have hut : ¬ (some u = some t) := hnz.2
        exact bud_other N t m pol L D _ hb hd hle hnz.1 h0' (by simp [hut])
  · cases rule_effect h with
    | drained i d hd hst _ =>
      refine bud_quiet N t m pol L D _ hb hd hle ?_ (by simp [Card.taken, Card.serving, hst])
      simp only [rem, hst]
      split <;> omega
    | reserved i d hd hst hnext =>
      refine bud_quiet N t m pol L D _ hb hd hle ?_ (by simp [Card.taken, Card.serving, hst, hnext])
      simp [rem, hst, hnext]
    | start i d u x hd hst hnext _ hnone =>
      have hpend : w.pending = false := by
        unfold World.pending
        rw [List.any_eq_false]
        intro c hc
        have := hnone c hc
        simpa using this
      exact absurd (by simp [begins, hpend]) hbeg
    | stop i d dur hd hidle =>
      exact bud_freed N t m pol L D _ hb hd hle (by simp [rem]) (by simp [Card.taken, Card.serving])
    | pass i d u mu hd hwin _ _ => exact absurd (by simp [begins]) hbeg
    | drain i d u mu hd hwin _ => exact absurd (by simp [begins]) hbeg

/-- What a card's clocks must say: its load took at most `L`, its turn did
not begin in the future, nor its load or its drain. -/
def CardOK (now : Nat) (c : Card T M C) : Prop :=
  c.load ≤ L ∧ (c.st = .up → c.turnAt ≤ now) ∧ ((c.st = .starting ∨ c.st = .draining) → c.since ≤ now)

theorem rule_ok {w w' : World T M C} {a : Action T M C} (hok : ∀ c ∈ w.cards, CardOK L w.now c)
    (h : w.rule = some (a, w')) : ∀ c ∈ w'.cards, CardOK L w.now c := by
  obtain ⟨i, c, c', hi, hs, hset, _⟩ := rule_step h
  intro e he
  rw [hset] at he
  rcases List.mem_or_eq_of_mem_set he with h1 | h1
  · exact hok e h1
  · subst h1
    have hc := hok c (List.mem_of_getElem? hi)
    cases hs with
    | drained _ _ => exact ⟨by simp, by simp, by simp⟩
    | reserved _ => exact ⟨by simp, by simp, by simp⟩
    | start _ _ _ => exact ⟨by simp, by simp, by simp⟩
    | stop _ _ => exact ⟨by simp, by simp, by simp⟩
    | pass _ _ hw =>
      have hup := (winner_old hw).1
      exact ⟨hc.1, fun _ => le_rfl, fun hx => by simp [hup] at hx⟩
    | drain _ _ _ => exact ⟨hc.1, by simp, fun _ => le_rfl⟩

theorem run_now : ∀ (fuel : Nat) (w : World T M C), (w.run fuel).2.now = w.now := by
  intro fuel
  induction fuel with
  | zero => intro w; rfl
  | succ n ih =>
    intro w
    cases hr : w.rule with
    | none => rw [run_none n hr]
    | some p =>
      obtain ⟨a, w'⟩ := p
      rw [run_some n hr]
      obtain ⟨_, _, _, _, _, _, hn⟩ := rule_step hr
      simp only
      rw [ih w', hn]

/-- **A round** keeps the cards within the budget. -/
theorem run_bud {C0 : Nat} : ∀ (fuel : Nat) {w : World T M C}, MWaiting N t m w.cards w.lines →
    (∀ c ∈ w.cards, CardOK L w.now c) → Bud N t m pol L D C0 w.cards w.lines w.now →
    (∀ a ∈ (w.run fuel).1, Spares m a) →
    MWaiting N t m (w.run fuel).2.cards (w.run fuel).2.lines ∧
      (∀ c ∈ (w.run fuel).2.cards, CardOK L w.now c) ∧
      Bud N t m pol L D C0 (w.run fuel).2.cards (w.run fuel).2.lines w.now := by
  intro fuel
  induction fuel with
  | zero => intro w hw hok hb _; exact ⟨hw, hok, hb⟩
  | succ n ih =>
    intro w hw hok hb hno
    cases hr : w.rule with
    | none =>
      rw [run_none n hr]
      exact ⟨hw, hok, hb⟩
    | some p =>
      obtain ⟨a, w'⟩ := p
      rw [run_some n hr] at hno ⊢
      have ha := hno a (List.mem_cons_self ..)
      obtain ⟨hw1, _⟩ := rule_multi N t m hw hr ha
      have hb1 := rule_bud N t m pol L D hw hb hr ha
      have hok1 := rule_ok L hok hr
      obtain ⟨_, _, _, _, _, _, hn⟩ := rule_step hr
      rw [← hn] at hb1 hok1
      have := ih hw1 hok1 hb1 fun b hb' => hno b (List.mem_cons_of_mem _ hb')
      rw [hn] at this
      exact this

/-- The cards, the lines, and the time. -/
structure TSys (T M C : Type) where
  sys : MSys T M C
  now : Nat

/-- What can happen, while the flow (`t`, `m`) stays queued, `m` is not
started and no card drains for it. -/
inductive TStep : TSys T M C → TSys T M C → Prop
  /-- requests come and go -/
  | busy (s : TSys T M C) (i : Nat) (c : Card T M C) (inflight busyAt : Nat) : s.sys.cards[i]? = some c →
      TStep s { s with sys := { s.sys with cards := s.sys.cards.set i { c with inflight := inflight, busyAt := busyAt } } }
  /-- a load finishes, having taken at most `L` -/
  | loaded (s : TSys T M C) (i : Nat) (c : Card T M C) (load : Nat) : s.sys.cards[i]? = some c →
      c.st = .starting → load ≤ L →
      TStep s { s with sys := { s.sys with cards := s.sys.cards.set i { c with st := .up, turnAt := s.now, busyAt := s.now, load := load } } }
  /-- a load fails, or a server dies at work -/
  | failed (s : TSys T M C) (i : Nat) (c : Card T M C) : s.sys.cards[i]? = some c → c.serving = true →
      TStep s { s with sys := { cards := s.sys.cards.set i { id := c.id }, lines := s.sys.lines.ended c.owner c.model } }
  /-- a server dies while it drains: the card has drained -/
  | died (s : TSys T M C) (i : Nat) (c : Card T M C) : s.sys.cards[i]? = some c → c.st = .draining →
      TStep s { s with sys := { s.sys with cards := s.sys.cards.set i { id := c.id, owner := c.owner, next := c.next } } }
  /-- a round, on whatever flows there are -/
  | round (s : TSys T M C) (flows : List (Flow T M)) (slots : M → Nat) :
      hasFlow flows t m = true → (s.sys.lines.join flows).tenants.length ≤ N →
      (∀ a ∈ (s.sys.round flows slots s.now pol).1, Spares m a) →
      TStep s { sys := (s.sys.round flows slots s.now pol).2, now := s.now }
  /-- a tick: a round would decide nothing, no load is overdue, and no
  requests in flight on a draining card are -/
  | tick (s : TSys T M C) (flows : List (Flow T M)) (slots : M → Nat) :
      hasFlow flows t m = true → (s.sys.lines.join flows).tenants.length ≤ N →
      (s.sys.world flows slots s.now pol).rule = none →
      (∀ c ∈ s.sys.cards, (c.st = .starting → s.now - c.since < L) ∧
        (c.st = .draining → 0 < c.inflight → s.now - c.since < D)) →
      TStep s { s with now := s.now + 1 }

/-- What stays true while the flow waits, in time. -/
structure TInv (C0 : Nat) (s : TSys T M C) : Prop where
  waiting : MWaiting N t m s.sys.cards s.sys.lines
  ok : ∀ c ∈ s.sys.cards, CardOK L s.now c
  bud : Bud N t m pol L D C0 s.sys.cards s.sys.lines s.now

/-- **No step leaves the budget.** -/
theorem step_inv {C0 : Nat} {s s' : TSys T M C} (hinv : TInv N t m pol L D C0 s)
    (h : TStep N t m pol L D s s') : TInv N t m pol L D C0 s' := by
  obtain ⟨hw, hok, hb⟩ := hinv
  cases h with
  | busy i c inflight busyAt hi =>
    obtain ⟨hw', he⟩ := mpot_congr N t m { c with inflight := inflight, busyAt := busyAt } hw hi
      (fun _ => rfl) (fun _ => rfl)
    refine ⟨hw', ?_, bud_quiet N t m pol L D _ hb hi (le_of_eq he) (le_of_eq rfl) rfl⟩
    intro e he'
    rcases List.mem_or_eq_of_mem_set he' with h1 | h1
    · exact hok e h1
    · subst h1
      exact hok c (List.mem_of_getElem? hi)
  | loaded i c load hi hst hload =>
    obtain ⟨hw', he⟩ := mpot_congr N t m { c with st := .up, turnAt := s.now, busyAt := s.now, load := load } hw hi
      (by intro v; simp [Card.taken, Card.serving, hst]) (by intro y; simp [Card.has, Card.serving, hst])
    refine ⟨hw', ?_, bud_quiet N t m pol L D _ hb hi (le_of_eq he) ?_ (by simp [Card.taken, Card.serving, hst])⟩
    · intro e he'
      rcases List.mem_or_eq_of_mem_set he' with h1 | h1
      · exact hok e h1
      · subst h1
        exact ⟨hload, fun _ => le_rfl, by simp⟩
    · simp only [rem, hst]
      omega
  | failed i c hi hs =>
    obtain ⟨hw', hle⟩ := mpot_ended N t m { id := c.id } hw hi hs (by simp [Card.taken, Card.serving])
    refine ⟨hw', ?_, bud_freed N t m pol L D _ hb hi hle (by simp [rem]) (by simp [Card.taken, Card.serving])⟩
    intro e he'
    rcases List.mem_or_eq_of_mem_set he' with h1 | h1
    · exact hok e h1
    · subst h1
      exact ⟨by simp, by simp, by simp⟩
  | died i c hi hst =>
    obtain ⟨hw', he⟩ := mpot_congr N t m { id := c.id, owner := c.owner, next := c.next } hw hi
      (by intro v; simp [Card.taken, Card.serving, hst]) (by intro y; simp [Card.has, Card.serving, hst])
    refine ⟨hw', ?_, bud_quiet N t m pol L D _ hb hi (le_of_eq he) ?_ (by simp [Card.taken, Card.serving, hst])⟩
    · intro e he'
      rcases List.mem_or_eq_of_mem_set he' with h1 | h1
      · exact hok e h1
      · subst h1
        exact ⟨by simp, by simp, by simp⟩
    · simp only [rem, hst]
      split <;> omega
  | round flows slots hq hfew hno =>
    obtain ⟨hwj, hj⟩ := mpot_join N t m hw hq hfew
    have hbj := bud_lines N t m pol L D hb hj
    obtain ⟨hw', hok', hb'⟩ := run_bud N t m pol L D (3 * s.sys.cards.length + 1)
      (w := s.sys.world flows slots s.now pol) hwj hok hbj hno
    exact ⟨hw', hok', hb'⟩
  | tick flows slots hq hfew hrule hover =>
    obtain ⟨hwj, _⟩ := mpot_join N t m hw hq hfew
    obtain ⟨hs1, _, _, hs4, _, hs6⟩ := settled hrule
    have hlostm : (s.sys.world flows slots s.now pol).placed m = false := not_placed_of_away m hwj.away
    have hlost : ((s.sys.world flows slots s.now pol).lost t).isSome = true := by
      unfold World.lost
      rw [List.find?_isSome]
      exact ⟨m, hwj.model, by simp [hlostm]⟩
    have hany : (s.sys.world flows slots s.now pol).anyLost = true := by
      unfold World.anyLost
      rw [List.any_eq_true]
      exact ⟨t, hwj.tenant, hlost⟩
    have hq1 : 1 ≤ qmax pol L := by unfold qmax; omega
    -- every card that matters has time left, and a tick takes one from it
    have key : ∀ c ∈ s.sys.cards,
        (heldIn s.sys.cards t = 0 ∨ (c.taken && Decidable.decide (c.owner = some t)) = true) →
        rem pol L D (s.now + 1) c + 1 ≤ rem pol L D s.now c := by
      intro c hc hcase
      obtain ⟨hload, hturn, hsince⟩ := hok c hc
      obtain ⟨hov1, hov2⟩ := hover c hc
      cases hst : c.st with
      | down => exact absurd hst (hs4 hany c hc).1
      | starting =>
        have := hov1 hst
        have := hsince (Or.inl hst)
        simp only [rem, hst]
        omega
      | draining =>
        have hin : 0 < c.inflight := Nat.pos_of_ne_zero (hs1 c hc hst)
        have := hov2 hst hin
        have := hsince (Or.inr hst)
        simp only [rem, hst]
        omega
      | up =>
        have hs : c.serving = true := by simp [Card.serving, hst]
        have hqm := quantum_le pol L hload
        have hyoung : s.now - c.turnAt < qmax pol L := by
          by_contra hold
          -- the turn is old: somebody wins it, and by `settled` it is the owner staying
          have h1 : pol.quantum c ≤ s.now - c.turnAt := by omega
          have h2 : c.turnAt < s.now := by omega
          obtain ⟨⟨u, mu⟩, hwin⟩ := Option.isSome_iff_exists.mp
            (winner_isSome (w := s.sys.world flows slots s.now pol) hst h1 h2 hwj.tenant hlost)
          obtain ⟨hu, hmu⟩ := hs6 c hc u mu hwin
          rcases hcase with h0 | hmine
          · -- `t` holds no card: the winner has rank 0, and the owner has not
            have hot : some t ≠ c.owner := by
              intro hx
              have := heldIn_pos hc (by simp [Card.taken, hs]) hx.symm
              omega
            have hr := (winner_first hwin hwj.tenant hlost hot h0).2
            simp only [World.rank, hu, ite_true] at hr
            omega
          · -- the card is `t`'s: it would move, not stay
            have hown : c.owner = some t := by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hmine
              exact hmine.2
            have hut : u = t := Option.some.inj (hu.trans hown)
            subst hut
            obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hlost
            have hmm := winner_lost hwin hm'
            subst hmm
            have h3 := lost_not_placed hm'
            have h4 : (s.sys.world flows slots s.now pol).placed mu = true := by
              unfold World.placed
              rw [List.any_eq_true]
              exact ⟨c, hc, by simp [Card.has, hs, hmu.symm]⟩
            rw [h3] at h4
            cases h4
        have := hturn hst
        simp only [rem, hst]
        omega
    refine ⟨hw, fun c hc => ?_, (show Bud N t m pol L D C0 s.sys.cards s.sys.lines (s.now + 1) from
      ⟨fun h0 c hc hp => ?_, fun h0 => ?_⟩)⟩
    · obtain ⟨h1, h2, h3⟩ := hok c hc
      exact ⟨h1, fun hx => Nat.le_succ_of_le (h2 hx), fun hx => Nat.le_succ_of_le (h3 hx)⟩
    · have := hb.1 h0 c hc hp
      have := key c hc (Or.inr hp)
      omega
    · obtain ⟨c, hc, hbc⟩ := hb.2 h0
      have := key c hc (Or.inl h0)
      exact ⟨c, hc, by omega⟩


/-- Any history of such steps. -/
inductive TTrace : TSys T M C → TSys T M C → Prop
  | nil (s : TSys T M C) : TTrace s s
  | step {s s1 s2 : TSys T M C} : TTrace s s1 → TStep N t m pol L D s1 s2 → TTrace s s2

/-- **No starvation, on any number of cards, in time.** While tenant `t`
has requests queued for model `m`, and until `m` is started or a card
begins to drain for it, at most `K * N * (D + L + Q)` ticks go by: whatever
else is queued, by whomever, whenever; whatever the model servers do
within their limits; on however many cards. -/
theorem mwait_bound {s s' : TSys T M C} {K : Nat} (h : TTrace N t m pol L D s s')
    (hw : MWaiting N t m s.sys.cards s.sys.lines) (hne : s.sys.cards ≠ [])
    (hok : ∀ c ∈ s.sys.cards, CardOK L s.now c) (hK : (s.sys.lines.models t).length ≤ K) :
    s'.now ≤ s.now + K * N * turn1 pol L D := by
  have hinv0 : TInv N t m pol L D
      (s.now + mPot N t m s.sys.cards s.sys.lines * turn1 pol L D + turn1 pol L D) s := by
    refine ⟨hw, hok, fun _ c _ _ => ?_, fun _ => ?_⟩
    · have := rem_le pol L D s.now c
      omega
    · obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
      refine ⟨c, by rw [hcs]; exact List.mem_cons_self .., ?_⟩
      have := rem_le pol L D s.now c
      omega
  have hinv : TInv N t m pol L D
      (s.now + mPot N t m s.sys.cards s.sys.lines * turn1 pol L D + turn1 pol L D) s' := by
    induction h with
    | nil => exact hinv0
    | step _ hs ih => exact step_inv N t m pol L D ih hs
  have hbase := bud_base N t m pol L D hinv.bud
  have h2 := mPot_le N t m hw hK
  have hKN : 1 ≤ K * N := by
    have := List.length_pos_of_mem hw.tenant
    have := hw.few
    have := List.length_pos_of_mem hw.model
    exact Nat.mul_pos (by omega) (by omega)
  have h4 := Nat.mul_le_mul_right (turn1 pol L D) h2
  have h5 : (K * N - 1) * turn1 pol L D + turn1 pol L D = K * N * turn1 pol L D := by
    obtain ⟨k, hk⟩ : ∃ k, K * N = k + 1 := ⟨K * N - 1, by omega⟩
    rw [hk]
    simp [Nat.add_mul]
  omega

end timed

assert_no_sorry rule_bud
assert_no_sorry step_inv
assert_no_sorry mwait_bound

end Timeshare
