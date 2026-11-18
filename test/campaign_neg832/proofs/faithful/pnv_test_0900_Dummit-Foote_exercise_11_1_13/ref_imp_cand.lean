import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_11_1_13_assumed {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (n : ℕ) (hn : n ≠ 0) : Module.rank ℚ (Fin n → ℝ) = 1 := by
  -- not proved: the reference statement is true, but the candidate incorrectly claims the ℚ-rank is 1
  sorry
