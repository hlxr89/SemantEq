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
  apply LinearEquiv.nonempty_equiv_iff_rank_eq.mpr
  have hn := dummy_assumed (n : ℕ) n.ne_zero
  have h₁ := dummy_assumed 1 one_ne_zero
  have hR : Module.rank ℚ ℝ = 1 :=
    (LinearEquiv.funUnique (Fin 1) ℚ ℝ).rank_eq.symm.trans h₁
  exact hn.trans hR.symm
