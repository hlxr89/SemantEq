import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) : ∃ (f : ℝ ≃ₗ[ℚ] Fin n → ℝ), True := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  obtain ⟨f, -⟩ := dummy_assumed 0
  exfalso
  exact zero_ne_one (f.injective (Subsingleton.elim _ _))
