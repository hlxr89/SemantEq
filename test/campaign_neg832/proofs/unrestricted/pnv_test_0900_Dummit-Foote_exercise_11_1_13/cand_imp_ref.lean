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
  have h := dummy_assumed 1 (by simp)
  rw [rank_fun, Real.rank_rat_real] at h
  have h' : Cardinal.continuum = 1 := by simpa using h
  have hle : Cardinal.aleph0 ≤ 1 := h' ▸ Cardinal.aleph0_le_continuum
  have htwo : (2 : Cardinal) < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  have : (2 : Cardinal) ≤ 1 := htwo.le.trans hle
  norm_num at this
