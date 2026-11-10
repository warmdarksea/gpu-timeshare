/-
Which request is answered next, on a model that is up: what `roundRobin`
guarantees for each free slot (`Picking.step`).

- `step_owner`: while the tenant whose turn it is holds fewer than half the
  card's slots and has a request to give, the slot is its. So the owner of
  a turn keeps at least half of it, whoever else has requests for the
  model: a tenant's turns cannot be taken from it by riding on them.
- `step_fewest`: otherwise the slot goes to a tenant with the fewest
  requests in flight among those with a request to give.
- `step_waiting`: so a tenant with a request to give and none in flight is
  not passed over for anybody who has one in flight: apart from the owner's
  half, nobody gets a second slot before it gets its first.

Latency on a model that is up is therefore a matter of single requests
ending, never of a turn: a tenant with nothing in flight has one of the
next `n + h` slots that come free, `n` the tenants with requests for the
model and `h` half a card's slots.
-/
import Timeshare.Proofs.MultiUp

namespace Timeshare

variable {T : Type} [DecidableEq T] {R K : Type} [DecidableEq K]

set_option linter.unusedSectionVars false

/-- One step of the search in `Picking.fewest`. -/
def fewStep (load : T → Nat) (best : Option (T × List R)) (p : T × List R) : Option (T × List R) :=
  if p.2.isEmpty then best else
  match best with
  | none => some p
  | some b => if load p.1 < load b.1 then some p else some b

/-- Whoever the search finds has a request to give, and no more in flight
than anybody else who has. -/
theorem fewStep_fold (load : T → Nat) : ∀ (l : List (T × List R)) (init : Option (T × List R)) (b : T × List R),
    l.foldl (fewStep load) init = some b →
    (∀ q, init = some q → load b.1 ≤ load q.1) ∧
    (∀ p ∈ l, p.2.isEmpty = false → load b.1 ≤ load p.1) ∧
    (init = some b ∨ (b ∈ l ∧ b.2.isEmpty = false)) := by
  intro l
  induction l with
  | nil =>
    intro init b h
    simp only [List.foldl_nil] at h
    exact ⟨fun q hq => (by rw [h] at hq; cases hq; exact le_rfl), fun p hp => (by simp at hp), Or.inl h⟩
  | cons a as ih =>
    intro init b h
    rw [List.foldl_cons] at h
    obtain ⟨h1, h2, h3⟩ := ih _ _ h
    by_cases hemp : a.2.isEmpty = true
    · -- nothing to give: the step keeps what it has
      have hs : fewStep load init a = init := by simp [fewStep, hemp]
      rw [hs] at h1 h3
      refine ⟨h1, fun p hp hne => ?_, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp'
        · rw [hemp] at hne; cases hne
        · exact h2 p hp' hne
      · rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr ⟨List.mem_cons_of_mem _ h3.1, h3.2⟩
    · have hne : a.2.isEmpty = false := by simpa using hemp
      cases init with
      | none =>
        have hs : fewStep load none a = some a := by simp [fewStep, hne]
        rw [hs] at h1 h3
        refine ⟨fun q hq => (by cases hq), fun p hp hpn => ?_, ?_⟩
        · rcases List.mem_cons.mp hp with rfl | hp'
          · exact h1 _ rfl
          · exact h2 p hp' hpn
        · rcases h3 with h3 | h3
          · cases h3; exact Or.inr ⟨List.mem_cons_self .., hne⟩
          · exact Or.inr ⟨List.mem_cons_of_mem _ h3.1, h3.2⟩
      | some q0 =>
        by_cases hlt : load a.1 < load q0.1
        · have hs : fewStep load (some q0) a = some a := by simp [fewStep, hne, hlt]
          rw [hs] at h1 h3
          have ha := h1 _ rfl
          refine ⟨fun q hq => (by cases hq; omega), fun p hp hpn => ?_, ?_⟩
          · rcases List.mem_cons.mp hp with rfl | hp'
            · exact ha
            · exact h2 p hp' hpn
          · rcases h3 with h3 | h3
            · cases h3; exact Or.inr ⟨List.mem_cons_self .., hne⟩
            · exact Or.inr ⟨List.mem_cons_of_mem _ h3.1, h3.2⟩
        · have hs : fewStep load (some q0) a = some q0 := by simp [fewStep, hne, hlt]
          rw [hs] at h1 h3
          have hq := h1 _ rfl
          refine ⟨fun q hq' => (by cases hq'; exact hq), fun p hp hpn => ?_, ?_⟩
          · rcases List.mem_cons.mp hp with rfl | hp'
            · omega
            · exact h2 p hp' hpn
          · rcases h3 with h3 | h3
            · exact Or.inl h3
            · exact Or.inr ⟨List.mem_cons_of_mem _ h3.1, h3.2⟩

/-- A line taken up from another place has the same tenants in it. -/
theorem mem_rotated {α : Type} (k : Nat) (l : List α) (p : α) : p ∈ l.drop k ++ l.take k ↔ p ∈ l := by
  rw [List.mem_append]
  constructor
  · rintro (hp | hp)
    · exact List.mem_of_mem_drop hp
    · exact List.mem_of_mem_take hp
  · intro hp
    rw [← List.take_append_drop k l] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact Or.inr hp
    · exact Or.inl hp

section step
variable (key : R → K) (le : T → T → Bool) (inflight : T → Nat) (own : Owner T)


/-- `fewest` finds a tenant with a request to give, and no more in flight
than anybody else who has one. -/
theorem fewest_spec {s : Picking T R K} {b : T × List R} (h : s.fewest key le inflight = some b) :
    b ∈ s.live key ∧ b.2.isEmpty = false ∧
      ∀ p ∈ s.live key, p.2.isEmpty = false → s.load inflight b.1 ≤ s.load inflight p.1 := by
  unfold Picking.fewest at h
  simp only at h
  obtain ⟨_, h2, h3⟩ := fewStep_fold (s.load inflight) _ none b h
  rcases h3 with h3 | h3
  · cases h3
  · exact ⟨(mem_rotated _ _ b).mp h3.1, h3.2, fun p hp hne => h2 p ((mem_rotated _ _ p).mpr hp) hne⟩

/-- **The owner's half.** While the tenant whose turn it is has a request
to give and holds fewer than half the card's slots, the next slot is its. -/
theorem step_owner {s s' : Picking T R K} {o : T} {p : T × List R}
    (h : s.step key le inflight own = some s') (ho : own.tenant = some o)
    (hp : (s.live key).find? (fun q => q.1 = o) = some p) (hne : p.2.isEmpty = false)
    (hhalf : own.held + s.got.count o < (own.slots + 1) / 2) : s'.got = o :: s.got := by
  have hown : s.owners key own = some p := by
    unfold Picking.owners
    simp [ho, hp, hne, hhalf]
  have hpo : p.1 = o := by
    have := List.find?_some hp
    simpa using this
  unfold Picking.step at h
  split at h
  · cases h
  · rw [hown] at h
    simp only [Option.getD_some] at h
    split at h
    · cases h
    · cases h
      simp [hpo]

/-- **Fewest in flight.** Otherwise the slot goes to a tenant with a
request to give and no more in flight than anybody else who has one. -/
theorem step_fewest {s s' : Picking T R K} (h : s.step key le inflight own = some s')
    (hown : s.owners key own = none) :
    ∃ u, s'.got = u :: s.got ∧
      ∀ p ∈ s.live key, p.2.isEmpty = false → s.load inflight u ≤ s.load inflight p.1 := by
  unfold Picking.step at h
  split at h
  · cases h
  · rename_i b hb
    rw [hown] at h
    simp only [Option.getD_none] at h
    obtain ⟨_, _, hmin⟩ := fewest_spec key le inflight hb
    split at h
    · cases h
    · cases h
      exact ⟨b.1, rfl, hmin⟩

/-- **Nobody waits behind a second slot.** A tenant with a request to give
and none in flight is not passed over, the owner's half aside, for anybody
who has one in flight. -/
theorem step_waiting {s s' : Picking T R K} {p : T × List R} (h : s.step key le inflight own = some s')
    (hown : s.owners key own = none) (hp : p ∈ s.live key) (hne : p.2.isEmpty = false)
    (h0 : s.load inflight p.1 = 0) : ∃ u, s'.got = u :: s.got ∧ s.load inflight u = 0 := by
  obtain ⟨u, hu, hmin⟩ := step_fewest key le inflight own h hown
  have := hmin p hp hne
  exact ⟨u, hu, by omega⟩

end step

assert_no_sorry step_owner
assert_no_sorry step_fewest
assert_no_sorry step_waiting

end Timeshare
