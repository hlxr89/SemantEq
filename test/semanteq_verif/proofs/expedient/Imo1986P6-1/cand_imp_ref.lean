import Mathlib

open Finset

-- ===== unified context (both sides' local defs, merged) =====
abbrev does_exist : Bool := true

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (S : Finset (ℤ × ℤ)) :
  ∃ (coloring : ℤ × ℤ → Bool),
    (∀ p ∈ S, coloring p = true ∨ coloring p = false) ∧
    (∀ x : ℤ, 
      let points_on_line := S.filter (fun p => p.1 = x)
      let red_count := (points_on_line.filter (fun p => coloring p = true)).card
      let white_count := (points_on_line.filter (fun p => coloring p = false)).card
      Int.natAbs (white_count - red_count) ≤ 1) ∧
    (∀ y : ℤ,
      let points_on_line := S.filter (fun p => p.2 = y)
      let red_count := (points_on_line.filter (fun p => coloring p = true)).card
      let white_count := (points_on_line.filter (fun p => coloring p = false)).card
      Int.natAbs (white_count - red_count) ≤ 1) := by
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
  classical
  obtain ⟨coloring, hc, hx, hy⟩ := problem_statement_assumed S
  let ε : ℤ × ℤ → ℤ := fun p => if coloring p = false then 1 else -1
  have sum_eq (T : Finset (ℤ × ℤ)) :
      ∑ p ∈ T, ε p = ((T.filter (fun p => coloring p = false)).card : ℤ) -
        ((T.filter (fun p => coloring p = true)).card : ℤ) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
      simp only [Finset.filter_insert]
      cases h : coloring a <;> simp [ε, ha, ih, h] <;> ring
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro p hp
    simp [ε]
  · intro x
    rw [sum_eq]
    have hb := hx x
    dsimp at hb
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hb
  · intro y
    rw [sum_eq]
    have hb := hy y
    dsimp at hb
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hb
