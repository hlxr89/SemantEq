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
theorem dummy (n : ℕ) : ∃ (f : ℝ ≃ₗ[ℚ] Fin n → ℝ), True := by
  -- not proved: the goal includes n = 0, while the antecedent only covers positive n
  sorry
