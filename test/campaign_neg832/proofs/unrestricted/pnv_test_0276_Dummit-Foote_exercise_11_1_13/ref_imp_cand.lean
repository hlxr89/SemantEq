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
theorem dummy {α : Type*} [Ring α] [IsDomain α] [CharZero α] (a : α) (n : ℕ) : a^n = a ↔ a = 1 ∨ n = 1 := by
  -- not proved: the candidate is false for a = 0 and n = 2, while the reference is consistent
  sorry
