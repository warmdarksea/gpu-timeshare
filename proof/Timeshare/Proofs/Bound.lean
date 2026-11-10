/-
No starvation, on one card, for any number of tenants and models:
`turns_bound`. While a flow (tenant `t`, model `m`) has queued requests,
at most `K * N - 1` turns begin before `m`'s own, whatever the other
tenants queue and whatever the model servers do -- `N` the most tenants
that have queued requests at one time, `K` the number of `t`'s models with
queued requests when the wait begins. With the turn that may be running
when the wait begins, that is doc/VERIFICATION.md §4.1's `T * k` turns.

The system: a state is the card and the lines (`Sys`). Between rounds the
world may do to the card what a model server can (`Env`): requests come
and go, a load finishes, a server fails. A round is `decide` on whatever
flows there are (`Sys.round`). `Trace` is any sequence of the two in which
the flow stays queued and `m` is not started, counting the turns begun (a
model started, or a turn passed from one tenant to another).

The proof is `pot` (Potential.lean): every step leaves it no higher, and
the beginning of a turn lowers it.
-/
import Timeshare.Proofs.Potential

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

/-! ### Who wins -/

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

/-- With no model on any card, the first in line gets a free card, for its
first model. -/
theorem claim_free {w : World T M C} {o : T} {x : M} {ts : List T} {ms : List M}
    (hfree : ∀ c ∈ w.cards, c.serving = false) (hts : w.lines.tenants = o :: ts)
    (hms : w.lines.models o = x :: ms) : w.claim = some (o, x) := by
  have hplaced : ∀ m, w.placed m = false := by
    intro m
    unfold World.placed
    rw [List.any_eq_false]
    intro c hc
    simp [hfree c hc]
  have hheld : ∀ u, w.held u = 0 := by
    intro u
    unfold World.held
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp [hfree c hc]
  have hlost : w.lost o = some x := by
    unfold World.lost
    rw [hms]
    simp [hplaced]
  unfold World.claim
  rw [hts]
  exact firstLowest_head (by simp [hlost]) fun u _ => by simp [hheld]

/-! ### One card -/

/-- The card and the lines: what there is between rounds. -/
structure Sys (T M C : Type) where
  card : Card T M C
  lines : Lines T M

/-- What the world may do to the card between rounds. -/
inductive Env : Sys T M C → Sys T M C → Prop
  /-- requests come and go -/
  | busy (s : Sys T M C) (inflight busyAt : Nat) :
      Env s { s with card := { s.card with inflight := inflight, busyAt := busyAt } }
  /-- the load finishes: the turn begins -/
  | loaded (s : Sys T M C) (now load : Nat) : s.card.st = .starting →
      Env s { s with card := { s.card with st := .up, turnAt := now, busyAt := now, load := load } }
  /-- a load fails, or a server dies at work: the turn is over (driver.go's `failed`) -/
  | failed (s : Sys T M C) : s.card.serving = true →
      Env s { card := { id := s.card.id }, lines := s.lines.ended s.card.owner s.card.model }
  /-- a server dies while it drains: its turn was over already -/
  | died (s : Sys T M C) : s.card.st = .draining → Env s { s with card := { id := s.card.id } }

/-- The world `decide` runs in. -/
def Sys.world (s : Sys T M C) (flows : List (Flow T M)) (slots : M → Nat) (now : Nat) (pol : Policy) :
    World T M C :=
  { cards := [s.card], flows, slots, lines := s.lines.join flows, now, pol }

/-- One round: `decide`'s actions, the card as they leave it, and the lines. -/
def Sys.round (s : Sys T M C) (flows : List (Flow T M)) (slots : M → Nat) (now : Nat) (pol : Policy) :
    List (Action T M C) × Sys T M C :=
  let r := (s.world flows slots now pol).run 4
  (r.1, { card := r.2.cards.headD s.card, lines := r.2.lines })

/-- A round is `decide`. -/
theorem round_decide (s : Sys T M C) (flows : List (Flow T M)) (slots : M → Nat) (now : Nat) (pol : Policy) :
    decide [s.card] flows slots s.lines now pol =
      ((s.round flows slots now pol).1, (s.round flows slots now pol).2.lines) := rfl

/-- How many turns begin in a round: a model is started, or a turn passes. -/
def turns (as : List (Action T M C)) : Nat := as.countP fun a => a.kind = .start ∨ a.kind = .pass

section bound
variable (N : Nat) (t : T) (m : M)

/-- Every tenant in the line has a model in its own. -/
def Lines.Full (l : Lines T M) : Prop := ∀ u ∈ l.tenants, l.models u ≠ []

/-- What stays true while the flow waits. -/
structure Waiting (c : Card T M C) (l : Lines T M) : Prop where
  nodup : l.Nodup
  full : l.Full
  tenant : t ∈ l.tenants
  model : m ∈ l.models t
  few : l.tenants.length ≤ N
  /-- `m` is not on the card -/
  away : c.serving = true → c.model ≠ some m

/-- The measure of a state: a turn that is running is counted as over. -/
def phi (c : Card T M C) (l : Lines T M) : Nat :=
  if c.serving = true then pot N t m l c.owner c.model else pot N t m l none none

omit [DecidableEq M] in
theorem full_tenantToBack {l : Lines T M} (o : Option T) (h : l.Full) : (l.tenantToBack o).Full := by
  intro u hu
  cases o with
  | none => exact h u hu
  | some v => exact h u (by simpa using hu)

theorem full_ended {l : Lines T M} (o : Option T) (x : Option M) (h : l.Full) : (l.ended o x).Full := by
  intro u hu
  have hu' : u ∈ l.tenants := by
    cases o with
    | none => simpa using hu
    | some v => simpa using hu
  have := h u hu'
  cases x with
  | none => simpa using this
  | some y =>
    simp only [ended_models]
    intro hnil
    have hlen := (toBack_perm (l.models u) y).length_eq
    rw [hnil] at hlen
    exact this (List.length_eq_zero_iff.mp hlen.symm)

theorem waiting_ended {c c' : Card T M C} {l : Lines T M} (o : Option T) (x : Option M)
    (h : Waiting N t m c l) (hc' : c'.serving = false) : Waiting N t m c' (l.ended o x) where
  nodup := ended_nodup o x h.nodup
  full := full_ended o x h.full
  tenant := by
    cases o with
    | none => simpa using h.tenant
    | some v => simpa using h.tenant
  model := by
    cases x with
    | none => simpa using h.model
    | some y => simpa using h.model
  few := by
    cases o with
    | none => simpa using h.few
    | some v => simpa [(toBack_perm l.tenants v).length_eq] using h.few
  away := by simp [hc']

omit [DecidableEq T] [DecidableEq M] in
@[simp] theorem serving_new (id : C) : ({ id := id } : Card T M C).serving = false := rfl

theorem phi_serving {c : Card T M C} (l : Lines T M) (h : c.serving = true) :
    phi N t m c l = pot N t m l c.owner c.model := by simp [phi, h]

theorem phi_idle {c : Card T M C} (l : Lines T M) (h : c.serving = false) :
    phi N t m c l = pot N t m l none none := by simp [phi, h]

/-- One rule, on one card, while the flow waits and `m` is not started:
the flow still waits, and the measure is no higher -- one lower if a turn
began. -/
theorem rule_single {w w' : World T M C} {a : Action T M C} {c : Card T M C} (hc : w.cards = [c])
    (hw : Waiting N t m c w.lines) (h : w.rule = some (a, w'))
    (hno : a.kind = .start → a.model ≠ some m) :
    ∃ c', w'.cards = [c'] ∧ Waiting N t m c' w'.lines ∧
      phi N t m c' w'.lines + turns [a] ≤ phi N t m c w.lines := by
  have hidx : ∀ {i : Nat} {d : Card T M C}, w.cards[i]? = some d → i = 0 ∧ d = c := by
    intro i d hd
    rw [hc] at hd
    cases i with
    | zero => simpa using hd.symm
    | succ i => simp at hd
  have hplaced : w.placed m = false := by
    unfold World.placed
    rw [hc]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases hs : c.serving = true
    · right; exact hw.away hs
    · left; simpa using hs
  cases rule_effect h with
  | drained i d hd hst _ =>
    obtain ⟨rfl, rfl⟩ := hidx hd
    have hs : d.serving = false := by simp [Card.serving, hst]
    refine ⟨{ id := d.id }, by simp [hc], ⟨hw.nodup, hw.full, hw.tenant, hw.model, hw.few, by simp⟩, ?_⟩
    rw [phi_idle N t m _ hs, phi_idle N t m _ (serving_new _)]
    simp [turns]
  | start i d o x hd hst hclaim =>
    obtain ⟨rfl, rfl⟩ := hidx hd
    have hs : d.serving = false := by simp [Card.serving, hst]
    obtain ⟨o', ts, hts⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hw.tenant)
    obtain ⟨x', ms, hms⟩ := List.exists_cons_of_ne_nil (hw.full o' (by rw [hts]; exact List.mem_cons_self ..))
    have hfree : ∀ e ∈ w.cards, e.serving = false := by
      intro e he
      rw [hc] at he
      simp only [List.mem_singleton] at he
      rw [he]; exact hs
    have hcl := claim_free hfree hts hms
    rw [hclaim] at hcl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hcl)
    have hxm : x ≠ m := fun hx => hno rfl (by rw [hx])
    have hs' : ({ id := d.id, st := .starting, model := some x, owner := some o } : Card T M C).serving = true := rfl
    refine ⟨{ id := d.id, st := .starting, model := some x, owner := some o }, by simp [hc], ⟨hw.nodup, hw.full, hw.tenant, hw.model, hw.few, ?_⟩, ?_⟩
    · intro _ hmod
      exact hxm (Option.some.inj hmod)
    · rw [phi_idle N t m _ hs, phi_serving N t m _ hs']
      have := pot_start (N := N) (m := m) hts hms hw.tenant hxm hw.few
      simpa [turns] using this
  | stop i d dur hd hidle =>
    obtain ⟨rfl, rfl⟩ := hidx hd
    have hup := (idleFor_spec hidle).1
    have hs : d.serving = true := by simp [Card.serving, hup]
    refine ⟨{ id := d.id }, by simp [hc], waiting_ended N t m _ _ hw (serving_new _), ?_⟩
    rw [phi_serving N t m _ hs, phi_idle N t m _ (serving_new _)]
    have := pot_ended (N := N) (o := d.owner) hw.nodup hw.tenant hw.model (hw.away hs) hw.few
    simpa [turns] using this
  | pass i d u mu hd hwin hown hmod =>
    obtain ⟨rfl, rfl⟩ := hidx hd
    have hup := (winner_old hwin).1
    have hs : d.serving = true := by simp [Card.serving, hup]
    have hs' : ({ d with owner := some u, turnAt := w.now } : Card T M C).serving = true := by
      simp [Card.serving, hup]
    -- `t` has a lost model: `m` is one
    have hlost : (w.lost t).isSome = true := by
      unfold World.lost
      rw [List.find?_isSome]
      exact ⟨m, hw.model, by simp [hplaced]⟩
    have hut : u ≠ t := by
      rintro rfl
      -- so it would move, not stay
      obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hlost
      have hmm := winner_lost hwin hm'
      subst hmm
      have h1 := lost_not_placed hm'
      have h2 : w.placed mu = true := by
        unfold World.placed
        rw [hc]
        simp [hs, hmod.symm]
      rw [h1] at h2
      cases h2
    -- and the turn goes to somebody before `t` in the line, unless it was `t`'s own
    have hfirst : d.owner = some t ∨ u ∈ before w.lines.tenants t := by
      by_cases hot : d.owner = some t
      · left; exact hot
      · right
        have hheld : w.held t = 0 := by
          unfold World.held
          rw [hc, List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro e he
          simp only [List.mem_singleton] at he
          subst he
          simp [hot]
        rcases (winner_first hwin hw.tenant hlost (fun h => hot h.symm) hheld).1 with h | h
        · exact absurd h hut
        · exact h
    refine ⟨{ d with owner := some u, turnAt := w.now }, by simp [hc], ⟨tenantToBack_nodup _ hw.nodup, full_tenantToBack _ hw.full, ?_,
      by simpa using hw.model, ?_, ?_⟩, ?_⟩
    · cases hown' : d.owner with
      | none => simpa using hw.tenant
      | some v => simpa using hw.tenant
    · cases hown' : d.owner with
      | none => simpa using hw.few
      | some v => simpa [(toBack_perm w.lines.tenants v).length_eq] using hw.few
    · intro _
      exact hw.away hs
    · rw [phi_serving N t m _ hs, phi_serving N t m _ hs']
      have := pot_pass (N := N) (m := m) (x := d.model) hw.nodup hw.tenant hut (winner_mem hwin) hown hfirst hw.few
      simpa [turns] using this
  | drain i d u mu hd hwin _ =>
    obtain ⟨rfl, rfl⟩ := hidx hd
    have hup := (winner_old hwin).1
    have hs : d.serving = true := by simp [Card.serving, hup]
    have hs' : ({ d with st := .draining } : Card T M C).serving = false := rfl
    refine ⟨{ d with st := .draining }, by simp [hc], waiting_ended N t m _ _ hw hs', ?_⟩
    rw [phi_serving N t m _ hs, phi_idle N t m _ hs']
    have := pot_ended (N := N) (o := d.owner) hw.nodup hw.tenant hw.model (hw.away hs) hw.few
    simpa [turns] using this
omit [DecidableEq T] [DecidableEq M] in
theorem turns_cons (a : Action T M C) (as : List (Action T M C)) : turns (a :: as) = turns [a] + turns as := by
  simp only [turns, List.countP_cons, List.countP_nil]
  omega

theorem run_some {w w' : World T M C} {a : Action T M C} (n : Nat) (hr : w.rule = some (a, w')) :
    w.run (n + 1) = (a :: (w'.run n).1, (w'.run n).2) := by
  simp [World.run, hr]

theorem run_none {w : World T M C} (n : Nat) (hr : w.rule = none) : w.run (n + 1) = ([], w) := by
  simp [World.run, hr]

/-- A whole round of rules. -/
theorem run_single : ∀ (fuel : Nat) {w : World T M C} {c : Card T M C}, w.cards = [c] →
    Waiting N t m c w.lines → (∀ a ∈ (w.run fuel).1, a.kind = .start → a.model ≠ some m) →
    ∃ c', (w.run fuel).2.cards = [c'] ∧ Waiting N t m c' (w.run fuel).2.lines ∧
      phi N t m c' (w.run fuel).2.lines + turns (w.run fuel).1 ≤ phi N t m c w.lines := by
  intro fuel
  induction fuel with
  | zero => intro w c hc hw _; exact ⟨c, hc, hw, by simp [World.run, turns]⟩
  | succ n ih =>
    intro w c hc hw hno
    cases hr : w.rule with
    | none =>
      rw [run_none n hr]
      exact ⟨c, hc, hw, by simp [turns]⟩
    | some p =>
      obtain ⟨a, w'⟩ := p
      rw [run_some n hr] at hno ⊢
      obtain ⟨c1, hc1, hw1, h1⟩ := rule_single N t m hc hw hr (hno a (List.mem_cons_self ..))
      obtain ⟨c2, hc2, hw2, h2⟩ := ih hc1 hw1 fun b hb => hno b (List.mem_cons_of_mem _ hb)
      refine ⟨c2, hc2, hw2, ?_⟩
      simp only
      rw [turns_cons]
      omega

/-- **A round**, while the flow waits and `m` is not started: the flow
still waits, and the measure has gone down by the turns begun. -/
theorem round_single {s : Sys T M C} {flows : List (Flow T M)} (slots : M → Nat) (now : Nat) (pol : Policy)
    (hw : Waiting N t m s.card s.lines) (hq : hasFlow flows t m = true)
    (hfew : (s.lines.join flows).tenants.length ≤ N)
    (hno : ∀ a ∈ (s.round flows slots now pol).1, a.kind = .start → a.model ≠ some m) :
    Waiting N t m (s.round flows slots now pol).2.card (s.round flows slots now pol).2.lines ∧
      phi N t m (s.round flows slots now pol).2.card (s.round flows slots now pol).2.lines +
        turns (s.round flows slots now pol).1 ≤ phi N t m s.card s.lines := by
  have hqt : hasQueued flows t = true := by
    simp only [hasFlow, hasQueued, List.any_eq_true, decide_eq_true_eq] at hq ⊢
    obtain ⟨f, hf, h1, _⟩ := hq
    exact ⟨f, hf, h1⟩
  have hwj : Waiting N t m s.card (s.lines.join flows) :=
    { nodup := join_nodup _ _
      full := by
        intro u hu
        have hu' := mem_join_tenants.mp hu
        simp only [hasQueued, List.any_eq_true, decide_eq_true_eq] at hu'
        obtain ⟨f, hf, rfl⟩ := hu'
        have : f.model ∈ (s.lines.join flows).models f.tenant :=
          mem_join_models.mpr (by
            simp only [hasFlow, List.any_eq_true, decide_eq_true_eq]
            exact ⟨f, hf, rfl, rfl⟩)
        exact List.ne_nil_of_mem this
      tenant := mem_join_tenants.mpr hqt
      model := mem_join_models.mpr hq
      few := hfew
      away := hw.away }
  have hphi : phi N t m s.card (s.lines.join flows) ≤ phi N t m s.card s.lines := by
    unfold phi
    split
    · exact pot_join _ _ hw.nodup hw.tenant hw.model hq
    · exact pot_join _ _ hw.nodup hw.tenant hw.model hq
  obtain ⟨c', hc', hw', h'⟩ := run_single N t m 4 (w := s.world flows slots now pol) (c := s.card) rfl hwj hno
  have hcard : (s.round flows slots now pol).2.card = c' := by
    show ((s.world flows slots now pol).run 4).2.cards.headD s.card = c'
    rw [hc']
    rfl
  rw [hcard]
  exact ⟨hw', le_trans h' hphi⟩

/-- **What the world does between rounds** does not raise the measure. -/
theorem env_single {s s' : Sys T M C} (hw : Waiting N t m s.card s.lines) (he : Env s s') :
    Waiting N t m s'.card s'.lines ∧ phi N t m s'.card s'.lines ≤ phi N t m s.card s.lines := by
  cases he with
  | busy inflight busyAt =>
    exact ⟨⟨hw.nodup, hw.full, hw.tenant, hw.model, hw.few, hw.away⟩, le_rfl⟩
  | loaded now load hst =>
    have hs : s.card.serving = true := by simp [Card.serving, hst]
    have hs' : ({ s.card with st := .up, turnAt := now, busyAt := now, load := load } : Card T M C).serving = true := rfl
    refine ⟨⟨hw.nodup, hw.full, hw.tenant, hw.model, hw.few, fun _ => hw.away hs⟩, ?_⟩
    rw [phi_serving N t m _ hs, phi_serving N t m _ hs']
  | failed hs =>
    refine ⟨waiting_ended N t m _ _ hw (serving_new _), ?_⟩
    rw [phi_serving N t m _ hs, phi_idle N t m _ (serving_new _)]
    exact pot_ended hw.nodup hw.tenant hw.model (hw.away hs) hw.few
  | died hst =>
    have hs : s.card.serving = false := by simp [Card.serving, hst]
    refine ⟨⟨hw.nodup, hw.full, hw.tenant, hw.model, hw.few, by simp⟩, ?_⟩
    rw [phi_idle N t m _ hs, phi_idle N t m _ (serving_new _)]

/-- Any history in which the flow (`t`, `m`) stays queued and `m` is not
started: rounds on whatever flows there are (at most `N` tenants with
queued requests at a time), and between them whatever the model servers
do. The number is the turns begun. -/
inductive Trace : Sys T M C → Nat → Sys T M C → Prop
  | nil (s : Sys T M C) : Trace s 0 s
  | env {s s1 s2 : Sys T M C} {n : Nat} : Trace s n s1 → Env s1 s2 → Trace s n s2
  | round {s s1 : Sys T M C} {n : Nat} (flows : List (Flow T M)) (slots : M → Nat) (now : Nat) (pol : Policy) :
      Trace s n s1 → hasFlow flows t m = true → (s1.lines.join flows).tenants.length ≤ N →
      (∀ a ∈ (s1.round flows slots now pol).1, a.kind = .start → a.model ≠ some m) →
      Trace s (n + turns (s1.round flows slots now pol).1) (s1.round flows slots now pol).2

/-- Along any such history the measure pays for every turn begun. -/
theorem trace_pot {s s' : Sys T M C} {n : Nat} (h : Trace N t m s n s') (hw : Waiting N t m s.card s.lines) :
    Waiting N t m s'.card s'.lines ∧ phi N t m s'.card s'.lines + n ≤ phi N t m s.card s.lines := by
  induction h with
  | nil => exact ⟨hw, by simp⟩
  | env _ he ih =>
    obtain ⟨hw1, h1⟩ := ih
    obtain ⟨hw2, h2⟩ := env_single N t m hw1 he
    exact ⟨hw2, by omega⟩
  | round flows slots now pol _ hq hfew hno ih =>
    obtain ⟨hw1, h1⟩ := ih
    obtain ⟨hw2, h2⟩ := round_single N t m slots now pol hw1 hq hfew hno
    exact ⟨hw2, by omega⟩

/-- The measure is at most `K * N - 1`, with `K` models in `t`'s line. -/
theorem phi_le {c : Card T M C} {l : Lines T M} {K : Nat} (hw : Waiting N t m c l)
    (hK : (l.models t).length ≤ K) : phi N t m c l ≤ K * N - 1 := by
  have hN : 1 ≤ N := by
    have := List.length_pos_of_mem hw.tenant
    have := hw.few
    omega
  have ha : ∀ x, aEff t m l x ≤ K - 1 := by
    intro x
    unfold aEff
    have h1 := List.length_filter_le (fun y => Decidable.decide (some y ≠ x)) (before (l.models t) m)
    have h2 := before_length_lt hw.model
    omega
  have hp : ∀ o, pEff N t l o ≤ N - 1 := fun o => pEff_le o hw.few hw.tenant
  have hK1 : 1 ≤ K := by
    have := List.length_pos_of_mem hw.model
    omega
  have key : ∀ o x, pot N t m l o x ≤ K * N - 1 := by
    intro o x
    unfold pot
    have h1 := Nat.mul_le_mul_right N (ha x)
    have h2 := hp o
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    have h3 : (k + 1) * N = k * N + N := by ring
    simp only [Nat.add_sub_cancel] at h1
    omega
  unfold phi
  split
  · exact key _ _
  · exact key _ _

/-- **No starvation, on one card.** While tenant `t` has requests queued
for model `m`, and until `m` is started, at most `K * N - 1` turns begin
(a model is started, or a turn passes from one tenant to another):
`N` the most tenants with queued requests at one time, `K` the number of
`t`'s models with queued requests when the wait begins. Whatever else is
queued, by whomever, whenever; whatever the model servers do. -/
theorem turns_bound {s s' : Sys T M C} {n K : Nat} (h : Trace N t m s n s')
    (hw : Waiting N t m s.card s.lines) (hK : (s.lines.models t).length ≤ K) : n ≤ K * N - 1 := by
  have h1 := (trace_pot N t m h hw).2
  have h2 := phi_le N t m hw hK
  omega

/-- New requests leave the flow waiting. -/
theorem waiting_join {c : Card T M C} {l : Lines T M} {flows : List (Flow T M)} (hw : Waiting N t m c l)
    (hq : hasFlow flows t m = true) (hfew : (l.join flows).tenants.length ≤ N) :
    Waiting N t m c (l.join flows) :=
  { nodup := join_nodup _ _
    full := by
      intro u hu
      have hu' := mem_join_tenants.mp hu
      simp only [hasQueued, List.any_eq_true, decide_eq_true_eq] at hu'
      obtain ⟨f, hf, rfl⟩ := hu'
      have : f.model ∈ (l.join flows).models f.tenant :=
        mem_join_models.mpr (by
          simp only [hasFlow, List.any_eq_true, decide_eq_true_eq]
          exact ⟨f, hf, rfl, rfl⟩)
      exact List.ne_nil_of_mem this
    tenant := by
      refine mem_join_tenants.mpr ?_
      simp only [hasFlow, hasQueued, List.any_eq_true, decide_eq_true_eq] at hq ⊢
      obtain ⟨f, hf, h1, _⟩ := hq
      exact ⟨f, hf, h1⟩
    model := mem_join_models.mpr hq
    few := hfew
    away := hw.away }

theorem phi_join {c : Card T M C} {l : Lines T M} {flows : List (Flow T M)} (hw : Waiting N t m c l)
    (hq : hasFlow flows t m = true) : phi N t m c (l.join flows) ≤ phi N t m c l := by
  unfold phi
  split
  · exact pot_join _ _ hw.nodup hw.tenant hw.model hq
  · exact pot_join _ _ hw.nodup hw.tenant hw.model hq

end bound

assert_no_sorry rule_single
assert_no_sorry round_single
assert_no_sorry env_single
assert_no_sorry turns_bound

end Timeshare
