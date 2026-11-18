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
theorem dummy : ∀ (n : ℕ), Module.rank ℚ (Fin n → ℚ) = 1 := by
  -- not proved: the candidate is false (for example at n = 0) and does not follow from the reference statement
  sorry
