/-
A round ends: `run_settles`. Every rule moves one card one step down the
ladder  up, turn old (3) > up, turn new / draining (2) > down (1) >
starting (0),  so a round is at most three decisions a card, and the fuel
`decide` gives `run` (3 a card, and one) is never what stops it.

(The step "up, turn old > up, turn new" is [Pass]. It is a step down only
because a turn that began this instant can't be taken: before that was a
rule, a timeslice of zero let two tenants on one model pass the turn for
ever, and Go's `Decide` did not return. This proof is how that was found.)
-/
import Timeshare.Proofs.Step

namespace Timeshare

variable {T M C : Type} [DecidableEq T] [DecidableEq M]

/-- How many more decisions a card can take part in, at time `now`. -/
def Card.steps (now : Nat) (c : Card T M C) : Nat :=
  match c.st with
  | .starting => 0
  | .down => 1
  | .draining => 2
  | .up => if now ≤ c.turnAt then 2 else 3

omit [DecidableEq T] [DecidableEq M] in
theorem Card.steps_le (now : Nat) (c : Card T M C) : c.steps now ≤ 3 := by
  unfold Card.steps
  split <;> try omega
  split <;> omega

/-- The decisions left in a round, at most. -/
def World.steps (w : World T M C) : Nat := (w.cards.map (Card.steps w.now)).sum

omit [DecidableEq T] [DecidableEq M] in
theorem World.steps_le (w : World T M C) : w.steps ≤ 3 * w.cards.length := by
  unfold World.steps
  induction w.cards with
  | nil => simp
  | cons c cs ih =>
    have := Card.steps_le w.now c
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem sum_set_lt {α : Type} (f : α → Nat) :
    ∀ (l : List α) (i : Nat) (x y : α), l[i]? = some x → f y < f x →
      ((l.set i y).map f).sum < (l.map f).sum := by
  intro l
  induction l with
  | nil => intro i x y h; simp at h
  | cons z zs ih =>
    intro i x y h hlt
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have := ih i x y h hlt
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

/-- Every `CardStep` is a step down. -/
theorem CardStep.steps_lt {w : World T M C} {c c' : Card T M C} (h : CardStep w c c') :
    c'.steps w.now < c.steps w.now := by
  cases h with
  | drained hdr _ => simp [Card.steps, hdr]
  | reserved hdown => simp [Card.steps, hdown]
  | start _ _ hdown => simp [Card.steps, hdown]

  | stop d hidle =>
    have hup := (idleFor_spec hidle).1
    simp only [Card.steps, hup]
    split <;> omega
  | pass t m hw =>
    obtain ⟨hup, -, hold⟩ := winner_old hw
    simp only [Card.steps, hup]
    have : ¬ w.now ≤ c.turnAt := by omega
    simp [this]
  | drain t m hw =>
    obtain ⟨hup, -, hold⟩ := winner_old hw
    simp only [Card.steps, hup]
    have : ¬ w.now ≤ c.turnAt := by omega
    simp [this]

/-- Every rule uses up a step. -/
theorem rule_steps_lt {w w' : World T M C} {a} (h : w.rule = some (a, w')) : w'.steps < w.steps := by
  obtain ⟨i, c, c', hi, hs, hset, hnow⟩ := rule_step h
  unfold World.steps
  rw [hset, hnow]
  exact sum_set_lt _ _ _ _ _ hi hs.steps_lt

/-- With more fuel than steps left, `run` stops because no rule applies. -/
theorem run_settles : ∀ (fuel : Nat) (w : World T M C), w.steps < fuel → (w.run fuel).2.rule = none := by
  intro fuel
  induction fuel with
  | zero => intro w h; omega
  | succ n ih =>
    intro w h
    unfold World.run
    cases hr : w.rule with
    | none => simpa using hr
    | some p =>
      obtain ⟨a, w'⟩ := p
      have := rule_steps_lt hr
      simp only
      exact ih w' (by omega)

/-- **A round settles.** `decide`'s fuel is enough: when it returns, no rule
applies. (Stated for the world `decide` runs in.) -/
theorem round_settles (w : World T M C) : (w.run (3 * w.cards.length + 1)).2.rule = none :=
  run_settles _ w (by have := w.steps_le; omega)

/-- A round is at most three decisions a card. -/
theorem run_length : ∀ (fuel : Nat) (w : World T M C), (w.run fuel).1.length ≤ w.steps := by
  intro fuel
  induction fuel with
  | zero => intro w; simp [World.run]
  | succ n ih =>
    intro w
    unfold World.run
    cases hr : w.rule with
    | none => simp
    | some p =>
      obtain ⟨a, w'⟩ := p
      have h1 := rule_steps_lt hr
      have h2 := ih w'
      simp only [List.length_cons]
      omega

assert_no_sorry round_settles
assert_no_sorry run_length

end Timeshare
