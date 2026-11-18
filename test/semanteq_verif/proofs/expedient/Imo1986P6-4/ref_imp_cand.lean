import Mathlib

open Finset

-- ===== unified context (both sides' local defs, merged) =====
abbrev does_exist : Bool := true

-- ===== assumed statement (antecedent) =====
theorem imo1986_p6_assumed (S : Finset (ℤ × ℤ)) :
    if does_exist then
      ∃ ε : ℤ × ℤ → ℤ,
        (∀ p ∈ S, ε p = 1 ∨ ε p = -1) ∧
        (∀ x : ℤ, |∑ p ∈ S.filter (fun p => p.1 = x), ε p| ≤ 1) ∧
        (∀ y : ℤ, |∑ p ∈ S.filter (fun p => p.2 = y), ε p| ≤ 1)
    else
      ¬ ∃ ε : ℤ × ℤ → ℤ,
        (∀ p ∈ S, ε p = 1 ∨ ε p = -1) ∧
        (∀ x : ℤ, |∑ p ∈ S.filter (fun p => p.1 = x), ε p| ≤ 1) ∧
        (∀ y : ℤ, |∑ p ∈ S.filter (fun p => p.2 = y), ε p| ≤ 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ (S : Finset (ℤ × ℤ)),
  ∃ (coloring : (ℤ × ℤ) → Bool),
    (∀ (x : ℤ),
      let white_points := Finset.filter (fun p => p.2 = x ∧ coloring p = true) S
      let red_points := Finset.filter (fun p => p.2 = x ∧ coloring p = false) S
      |(white_points.card : ℤ) - (red_points.card : ℤ)| ≤ 1) ∧
    (∀ (y : ℤ),
      let white_points := Finset.filter (fun p => p.1 = y ∧ coloring p = true) S
      let red_points := Finset.filter (fun p => p.1 = y ∧ coloring p = false) S
      |(white_points.card : ℤ) - (red_points.card : ℤ)| ≤ 1) := by
  intro S
  obtain ⟨ε, hε, hx, hy⟩ := imo1986_p6_assumed S
  let coloring : ℤ × ℤ → Bool := fun p => if ε p = 1 then true else false
  have sum_eq (T : Finset (ℤ × ℤ)) (hT : ∀ p ∈ T, ε p = 1 ∨ ε p = -1)
      (q : ℤ × ℤ → Prop) [DecidablePred q] :
      ∑ p ∈ T.filter q, ε p =
        ((T.filter (fun p => q p ∧ coloring p = true)).card : ℤ) -
        ((T.filter (fun p => q p ∧ coloring p = false)).card : ℤ) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
        have hi := ih (fun p hp => hT p (Finset.mem_insert_of_mem hp))
        rcases hT a (Finset.mem_insert_self a T) with h | h
        · by_cases hq : q a <;>
            simp [Finset.filter_insert, ha, hq, h, coloring] at hi ⊢ <;> omega
        · by_cases hq : q a <;>
            simp [Finset.filter_insert, ha, hq, h, coloring] at hi ⊢ <;> omega
  refine ⟨coloring, ?_, ?_⟩
  · intro x
    dsimp
    rw [← sum_eq S hε (fun p => p.2 = x)]
    exact hy x
  · intro y
    dsimp
    rw [← sum_eq S hε (fun p => p.1 = y)]
    exact hx y
