import Mathlib

open Finset

-- ===== unified context (both sides' local defs, merged) =====
abbrev does_exist : Bool := true

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
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
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo1986_p6 (S : Finset (ℤ × ℤ)) :
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
  obtain ⟨coloring, hx, hy⟩ := problem_statement_assumed S
  let ε : ℤ × ℤ → ℤ := fun p => if coloring p then 1 else -1
  have sum_eq (T : Finset (ℤ × ℤ)) (q : ℤ × ℤ → Prop) [DecidablePred q] :
      ∑ p ∈ T.filter q, ε p =
        ((T.filter (fun p => q p ∧ coloring p = true)).card : ℤ) -
        ((T.filter (fun p => q p ∧ coloring p = false)).card : ℤ) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
        cases h : coloring a <;>
          by_cases hq : q a <;>
            simp [Finset.filter_insert, ha, hq, h, ε] at ih ⊢ <;> omega
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro p hp
    cases h : coloring p <;> simp [ε, h]
  · intro x
    rw [sum_eq S (fun p => p.1 = x)]
    exact hy x
  · intro y
    rw [sum_eq S (fun p => p.2 = y)]
    exact hx y
