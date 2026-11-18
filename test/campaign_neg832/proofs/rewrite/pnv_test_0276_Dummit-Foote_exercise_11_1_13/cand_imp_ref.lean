import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [Ring α] [IsDomain α] [CharZero α] (a : α) (n : ℕ) : a^n = a ↔ a = 1 ∨ n = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  -- not proved: the statements are unrelated; deriving the reference through the false candidate assumption would require the prohibited manufacture of False
  sorry
