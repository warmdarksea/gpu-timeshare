/-
No starvation, on one card, in time: `wait_bound`. A flow with queued
requests waits at most `K * N * (L + Q + D)` ticks for its model to be
started -- `L` the longest load, `D` the longest any requests in flight
take, `Q` the longest quantum (and at least one tick, so a quantum of zero
is covered), `N` the most tenants with queued requests at a time, `K` the
number of the flow's tenant's models with queued requests when the wait
begins.

Time is in ticks, and the scheduler has had its say before each one: time
moves only from a state in which a round would decide nothing (`tick`),
as in spec/Turns.tla. Everything else happens at an instant: rounds, and
what the model servers do. A load that has taken `L` must finish or fail
before the next tick, and requests in flight on a draining card end
within `D`.

The proof: `budget` = the time now + the turns that can still begin
(`phi`, Bound.lean) times the longest turn + the time left in the turn
that is running (`remc`). No step raises it. A tick lowers the time left
by one -- there is always some left, because a settled state has no free
card, no drained card and no turn that is old (Progress.lean).
-/
import Timeshare.Proofs.Progress

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

theorem mul_step {a b k : Nat} (h : a + 1 ≤ b) : a * k + k ≤ b * k := by
  have := Nat.mul_le_mul_right k h
  rw [Nat.add_mul, Nat.one_mul] at this
  exact this

section timed
variable (N : Nat) (t : T) (m : M) (pol : Policy) (L D : Nat)

/-- The longest quantum, for loads of at most `L`; and at least one tick:
a turn that began this instant can't be taken. -/
def qmax : Nat := max (max pol.maxTimeslice (pol.loadRatio * L)) 1

/-- The longest turn: a load, a quantum, a drain. -/
def turn1 : Nat := L + qmax pol L + D

omit [DecidableEq T] [DecidableEq M] in
theorem quantum_le {c : Card T M C} (h : c.load ≤ L) : pol.quantum c ≤ qmax pol L := by
  unfold Policy.quantum qmax
  have := Nat.mul_le_mul_left pol.loadRatio h
  omega

/-- The time left in what the card is doing: `since` is when it began to
load, or to drain. -/
def remc (now since : Nat) (c : Card T M C) : Nat :=
  match c.st with
  | .down => 0
  | .starting => (L - (now - since)) + qmax pol L + D
  | .up => (qmax pol L - (now - c.turnAt)) + D
  | .draining => D - (now - since)

omit [DecidableEq T] [DecidableEq M] in
theorem remc_le (now since : Nat) (c : Card T M C) : remc pol L D now since c ≤ turn1 pol L D := by
  unfold remc turn1
  split <;> omega

/-- One rule, in time: with the card's clock restarted, the budget is no
higher. -/
theorem rule_timed {w w' : World T M C} {a : Action T M C} {c : Card T M C} (since : Nat)
    (hc : w.cards = [c]) (hw : Waiting N t m c w.lines) (hl : c.load ≤ L)
    (h : w.rule = some (a, w')) (hno : a.kind = .start → a.model ≠ some m) :
    ∃ c', w'.cards = [c'] ∧ w'.now = w.now ∧ Waiting N t m c' w'.lines ∧ c'.load ≤ L ∧
      (c'.st = .up → c'.turnAt ≤ w.now) ∧
      phi N t m c' w'.lines * turn1 pol L D + remc pol L D w.now w.now c' ≤
        phi N t m c w.lines * turn1 pol L D + remc pol L D w.now since c := by
  obtain ⟨c1, hc1, hw1, hphi⟩ := rule_single N t m hc hw h hno
  have hnow : w'.now = w.now := by
    obtain ⟨_, _, _, _, _, _, hn⟩ := rule_step h
    exact hn
  have hidx : ∀ {i : Nat} {d : Card T M C}, w.cards[i]? = some d → i = 0 ∧ d = c := by
    intro i d hd
    rw [hc] at hd
    cases i with
    | zero => simpa using hd.symm
    | succ i => simp at hd
  refine ⟨c1, hc1, hnow, hw1, ?_⟩
  cases rule_effect h with
  | drained i d hd hst _ =>
    obtain ⟨rfl, rfl⟩ := hidx hd
    have : c1 = { id := d.id } := by simpa [hc] using hc1.symm
    subst this
    have h1 := Nat.mul_le_mul_right (turn1 pol L D) (show phi N t m _ _ ≤ phi N t m d w.lines by simpa [turns] using hphi)
    refine ⟨by simp, by simp, ?_⟩
    simp only [remc]
    omega
  | start i d o x hd hst _ =>
    obtain ⟨rfl, rfl⟩ := hidx hd
    have : c1 = { id := d.id, st := .starting, model := some x, owner := some o } := by simpa [hc] using hc1.symm
    subst this
    have h1 := mul_step (k := turn1 pol L D) (show phi N t m _ _ + 1 ≤ phi N t m d w.lines by simpa [turns] using hphi)
    refine ⟨by simp, by simp, ?_⟩
    simp only [remc, hst, turn1] at h1 ⊢
    omega
  | stop i d dur hd hidle =>
    obtain ⟨rfl, rfl⟩ := hidx hd
    have : c1 = { id := d.id } := by simpa [hc] using hc1.symm
    subst this
    have h1 := Nat.mul_le_mul_right (turn1 pol L D) (show phi N t m _ _ ≤ phi N t m d w.lines by simpa [turns] using hphi)
    refine ⟨by simp, by simp, ?_⟩
    simp only [remc]
    omega
  | pass i d u mu hd hwin _ _ =>
    obtain ⟨rfl, rfl⟩ := hidx hd
    have hup := (winner_old hwin).1
    have : c1 = { d with owner := some u, turnAt := w.now } := by simpa [hc] using hc1.symm
    subst this
    have h1 := mul_step (k := turn1 pol L D) (show phi N t m _ _ + 1 ≤ phi N t m d w.lines by simpa [turns] using hphi)
    refine ⟨hl, fun _ => le_rfl, ?_⟩
    simp only [remc, hup, turn1] at h1 ⊢
    omega
  | drain i d u mu hd hwin _ =>
    obtain ⟨rfl, rfl⟩ := hidx hd
    have hup := (winner_old hwin).1
    have : c1 = { d with st := .draining } := by simpa [hc] using hc1.symm
    subst this
    have h1 := Nat.mul_le_mul_right (turn1 pol L D) (show phi N t m _ _ ≤ phi N t m d w.lines by simpa [turns] using hphi)
    refine ⟨hl, by simp, ?_⟩
    simp only [remc, hup]
    omega

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

/-- A whole round, in time. If it decided anything, the card's clock
restarts. -/
theorem run_timed : ∀ (fuel : Nat) {w : World T M C} {c : Card T M C} (since : Nat), w.cards = [c] →
    Waiting N t m c w.lines → c.load ≤ L → (c.st = .up → c.turnAt ≤ w.now) →
    (∀ a ∈ (w.run fuel).1, a.kind = .start → a.model ≠ some m) →
    ∃ c', (w.run fuel).2.cards = [c'] ∧ Waiting N t m c' (w.run fuel).2.lines ∧ c'.load ≤ L ∧
      (c'.st = .up → c'.turnAt ≤ w.now) ∧
      phi N t m c' (w.run fuel).2.lines * turn1 pol L D +
          remc pol L D w.now (if (w.run fuel).1 = [] then since else w.now) c' ≤
        phi N t m c w.lines * turn1 pol L D + remc pol L D w.now since c := by
  intro fuel
  induction fuel with
  | zero => intro w c since hc hw hl ht _; exact ⟨c, hc, hw, hl, ht, by simp [World.run]⟩
  | succ n ih =>
    intro w c since hc hw hl ht hno
    cases hr : w.rule with
    | none =>
      rw [run_none n hr]
      exact ⟨c, hc, hw, hl, ht, by simp⟩
    | some p =>
      obtain ⟨a, w'⟩ := p
      rw [run_some n hr] at hno ⊢
      obtain ⟨c1, hc1, hn1, hw1, hl1, ht1, h1⟩ :=
        rule_timed N t m pol L D since hc hw hl hr (hno a (List.mem_cons_self ..))
      obtain ⟨c2, hc2, hw2, hl2, ht2, h2⟩ :=
        ih w.now hc1 hw1 hl1 (by rw [hn1]; exact ht1) fun b hb => hno b (List.mem_cons_of_mem _ hb)
      rw [hn1] at h2 ht2
      refine ⟨c2, hc2, hw2, hl2, ht2, ?_⟩
      simp only [reduceCtorEq, ite_false]
      have : (if (w'.run n).1 = [] then w.now else w.now) = w.now := by split <;> rfl
      rw [this] at h2
      omega

/-- The card, the lines, and the time. -/
structure TSys (T M C : Type) where
  sys : Sys T M C
  now : Nat
  /-- when the card began to load, or to drain -/
  since : Nat

/-- A round now. -/
def TSys.round (s : TSys T M C) (flows : List (Flow T M)) (slots : M → Nat) :
    List (Action T M C) × TSys T M C :=
  let r := s.sys.round flows slots s.now pol
  (r.1, { sys := r.2, now := s.now, since := if r.1 = [] then s.since else s.now })

/-- What can happen, while the flow (`t`, `m`) stays queued and `m` is not
started. -/
inductive TStep : TSys T M C → TSys T M C → Prop
  /-- requests come and go -/
  | busy (s : TSys T M C) (inflight busyAt : Nat) :
      TStep s { s with sys := { s.sys with card := { s.sys.card with inflight := inflight, busyAt := busyAt } } }
  /-- the load finishes, having taken at most `L` -/
  | loaded (s : TSys T M C) (load : Nat) : s.sys.card.st = .starting → load ≤ L →
      TStep s { s with sys := { s.sys with card :=
        { s.sys.card with st := .up, turnAt := s.now, busyAt := s.now, load := load } } }
  /-- a load fails, or a server dies at work -/
  | failed (s : TSys T M C) : s.sys.card.serving = true →
      TStep s { s with sys := { card := { id := s.sys.card.id },
                                lines := s.sys.lines.ended s.sys.card.owner s.sys.card.model } }
  /-- a server dies while it drains -/
  | died (s : TSys T M C) : s.sys.card.st = .draining →
      TStep s { s with sys := { s.sys with card := { id := s.sys.card.id } } }
  /-- a round, on whatever flows there are -/
  | round (s : TSys T M C) (flows : List (Flow T M)) (slots : M → Nat) :
      hasFlow flows t m = true → (s.sys.lines.join flows).tenants.length ≤ N →
      (∀ a ∈ (s.round pol flows slots).1, a.kind = .start → a.model ≠ some m) →
      TStep s (s.round pol flows slots).2
  /-- a tick: a round would decide nothing, no load is overdue, and no
  requests in flight on a draining card are -/
  | tick (s : TSys T M C) (flows : List (Flow T M)) (slots : M → Nat) :
      hasFlow flows t m = true → (s.sys.lines.join flows).tenants.length ≤ N →
      (s.sys.world flows slots s.now pol).rule = none →
      (s.sys.card.st = .starting → s.now - s.since < L) →
      (s.sys.card.st = .draining → 0 < s.sys.card.inflight → s.now - s.since < D) →
      TStep s { s with now := s.now + 1 }

/-- What stays true while the flow waits, in time. -/
structure TWaiting (s : TSys T M C) : Prop where
  waiting : Waiting N t m s.sys.card s.sys.lines
  load : s.sys.card.load ≤ L
  turn : s.sys.card.st = .up → s.sys.card.turnAt ≤ s.now
  since : s.since ≤ s.now

/-- The time now, the turns that can still begin, and the time left in
the one that is running. -/
def budget (s : TSys T M C) : Nat :=
  s.now + phi N t m s.sys.card s.sys.lines * turn1 pol L D + remc pol L D s.now s.since s.sys.card

/-- **No step raises the budget.** -/
theorem step_budget {s s' : TSys T M C} (hw : TWaiting N t m L s) (h : TStep N t m pol L D s s') :
    TWaiting N t m L s' ∧ budget N t m pol L D s' ≤ budget N t m pol L D s := by
  cases h with
  | busy inflight busyAt =>
    exact ⟨⟨⟨hw.waiting.nodup, hw.waiting.full, hw.waiting.tenant, hw.waiting.model, hw.waiting.few,
      hw.waiting.away⟩, hw.load, hw.turn, hw.since⟩, le_rfl⟩
  | loaded load hst hload =>
    have hs : s.sys.card.serving = true := by simp [Card.serving, hst]
    have hs' : ({ s.sys.card with st := .up, turnAt := s.now, busyAt := s.now, load := load } :
        Card T M C).serving = true := rfl
    refine ⟨⟨⟨hw.waiting.nodup, hw.waiting.full, hw.waiting.tenant, hw.waiting.model, hw.waiting.few,
      fun _ => hw.waiting.away hs⟩, hload, fun _ => le_rfl, hw.since⟩, ?_⟩
    simp only [budget, phi_serving N t m _ hs, phi_serving N t m _ hs', remc, hst]
    omega
  | failed hs =>
    obtain ⟨hw', hphi⟩ := env_single N t m hw.waiting (Env.failed s.sys hs)
    refine ⟨⟨hw', by simp, by simp, hw.since⟩, ?_⟩
    have h1 := Nat.mul_le_mul_right (turn1 pol L D) hphi
    simp only [budget, remc] at h1 ⊢
    omega
  | died hst =>
    obtain ⟨hw', hphi⟩ := env_single N t m hw.waiting (Env.died s.sys hst)
    refine ⟨⟨hw', by simp, by simp, hw.since⟩, ?_⟩
    have h1 := Nat.mul_le_mul_right (turn1 pol L D) hphi
    simp only [budget, remc] at h1 ⊢
    omega
  | round flows slots hq hfew hno =>
    have hwj := waiting_join N t m hw.waiting hq hfew
    have hphi := Nat.mul_le_mul_right (turn1 pol L D) (phi_join N t m hw.waiting hq)
    obtain ⟨c', hc', hw', hl', ht', h'⟩ :=
      run_timed N t m pol L D 4 (w := s.sys.world flows slots s.now pol) (c := s.sys.card) s.since rfl hwj
        hw.load hw.turn hno
    have hcard : (s.round pol flows slots).2.sys.card = c' := by
      show ((s.sys.world flows slots s.now pol).run 4).2.cards.headD s.sys.card = c'
      rw [hc']
      rfl
    refine ⟨⟨by rw [hcard]; exact hw', by rw [hcard]; exact hl', by rw [hcard]; exact ht', ?_⟩, ?_⟩
    · show (if _ then s.since else s.now) ≤ s.now
      split
      · exact hw.since
      · exact le_rfl
    · show s.now + phi N t m (s.round pol flows slots).2.sys.card _ * _ +
          remc pol L D s.now (if ((s.sys.world flows slots s.now pol).run 4).1 = [] then s.since else s.now)
            (s.round pol flows slots).2.sys.card ≤ _
      rw [hcard]
      have h'' : phi N t m c' ((s.sys.world flows slots s.now pol).run 4).2.lines * turn1 pol L D +
          remc pol L D s.now (if ((s.sys.world flows slots s.now pol).run 4).1 = [] then s.since else s.now) c' ≤
          phi N t m s.sys.card (s.sys.lines.join flows) * turn1 pol L D + remc pol L D s.now s.since s.sys.card := h'
      unfold budget
      have : (s.round pol flows slots).2.sys.lines = ((s.sys.world flows slots s.now pol).run 4).2.lines := rfl
      rw [this]
      omega
  | tick flows slots hq hfew hrule hload hdrain =>
    have hwj := waiting_join N t m hw.waiting hq hfew
    have hcards : (s.sys.world flows slots s.now pol).cards = [s.sys.card] := rfl
    have hq1 : 1 ≤ qmax pol L := by unfold qmax; omega
    have hqm := quantum_le pol L hw.load
    refine ⟨⟨hw.waiting, hw.load, fun h => le_trans (hw.turn h) (Nat.le_succ _),
      le_trans hw.since (Nat.le_succ _)⟩, ?_⟩
    have hrem : remc pol L D (s.now + 1) s.since s.sys.card + 1 ≤ remc pol L D s.now s.since s.sys.card := by
      have hsince := hw.since
      cases hst : s.sys.card.st with
      | down => exact absurd hrule (progress_free N t m hcards hst hwj)
      | starting =>
        have := hload hst
        simp only [remc, hst]
        omega
      | up =>
        have hturn := hw.turn hst
        have hnot : ¬ (pol.quantum s.sys.card ≤ s.now - s.sys.card.turnAt ∧ s.sys.card.turnAt < s.now) := by
          rintro ⟨h1, h2⟩
          exact progress_old N t m hcards hst h1 h2 hwj hrule
        simp only [remc, hst]
        omega
      | draining =>
        have hin : 0 < s.sys.card.inflight := by
          by_contra h0
          exact progress_drained hcards hst (by omega) hrule
        have := hdrain hst hin
        simp only [remc, hst]
        omega
    simp only [budget]
    omega

/-- Any history of such steps. -/
inductive TTrace : TSys T M C → TSys T M C → Prop
  | nil (s : TSys T M C) : TTrace s s
  | step {s s1 s2 : TSys T M C} : TTrace s s1 → TStep N t m pol L D s1 s2 → TTrace s s2

theorem trace_budget {s s' : TSys T M C} (h : TTrace N t m pol L D s s') (hw : TWaiting N t m L s) :
    TWaiting N t m L s' ∧ budget N t m pol L D s' ≤ budget N t m pol L D s := by
  induction h with
  | nil => exact ⟨hw, le_rfl⟩
  | step _ hs ih =>
    obtain ⟨hw1, h1⟩ := ih
    obtain ⟨hw2, h2⟩ := step_budget N t m pol L D hw1 hs
    exact ⟨hw2, le_trans h2 h1⟩

/-- **No starvation, on one card, in time.** While tenant `t` has requests
queued for model `m`, and until `m` is started, at most
`K * N * (L + Q + D)` ticks go by: whatever else is queued, by whomever,
whenever; whatever the model servers do within their limits. -/
theorem wait_bound {s s' : TSys T M C} {K : Nat} (h : TTrace N t m pol L D s s')
    (hw : TWaiting N t m L s) (hK : (s.sys.lines.models t).length ≤ K) :
    s'.now ≤ s.now + K * N * turn1 pol L D := by
  have h1 := (trace_budget N t m pol L D h hw).2
  have h2 := phi_le N t m hw.waiting hK
  have h3 := remc_le pol L D s.now s.since s.sys.card
  have hKN : 1 ≤ K * N := by
    have := List.length_pos_of_mem hw.waiting.tenant
    have := hw.waiting.few
    have := List.length_pos_of_mem hw.waiting.model
    exact Nat.mul_pos (by omega) (by omega)
  have h4 := Nat.mul_le_mul_right (turn1 pol L D) h2
  have h5 : (K * N - 1) * turn1 pol L D + turn1 pol L D = K * N * turn1 pol L D := by
    obtain ⟨k, hk⟩ : ∃ k, K * N = k + 1 := ⟨K * N - 1, by omega⟩
    rw [hk]
    simp [Nat.add_mul]
  unfold budget at h1
  omega

end timed

assert_no_sorry rule_timed
assert_no_sorry step_budget
assert_no_sorry wait_bound

end Timeshare
