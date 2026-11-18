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
  have hfun : Module.rank ℚ (Fin n → ℝ) = 1 :=
    dummy_assumed n n.ne_zero
  have hreal : Module.rank ℚ ℝ = 1 := by
    have h := dummy_assumed 1 (by norm_num)
    rw [(LinearEquiv.piUnique ℚ (fun _ : Fin 1 => ℝ)).rank_eq] at h
    exact h
  apply LinearEquiv.nonempty_equiv_iff_lift_rank_eq.mpr
  rw [hfun, hreal]
