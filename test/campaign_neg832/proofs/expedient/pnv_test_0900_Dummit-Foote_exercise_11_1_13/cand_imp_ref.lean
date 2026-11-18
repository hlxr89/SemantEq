import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) (hn : n ≠ 0) : Module.rank ℚ (Fin n → ℝ) = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  have h := dummy_assumed 1 (by norm_num)
  rw [rank_pi, Real.rank_rat_real] at h
  have hc : Cardinal.continuum = 1 := by simpa using h
  exfalso
  exact (Cardinal.nat_lt_continuum 1).ne hc.symm
