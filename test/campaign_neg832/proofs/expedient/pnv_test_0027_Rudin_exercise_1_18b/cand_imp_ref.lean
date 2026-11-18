import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} {x : EuclideanSpace ℚ (Fin n)} (h : ∑ i, x i = 0): ∃ (y : EuclideanSpace ℚ (Fin n)), y ≠ 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_18b
  : ∀ (x : ℝ), x ≠ 0 → ¬ ∃ (y : ℝ), y ≠ 0 ∧ x * y = 0 := by
  rintro x hx ⟨y, hy, hxy⟩
  exact (mul_ne_zero hx hy) hxy
