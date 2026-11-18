import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {r : ℚ} (hr : r ≠ 0) {x : ℝ} (hx : ¬ Irrational x) : Irrational (r * x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1b
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( Irrational x ) -> Irrational ( x * y ) := by
  have hzero : Irrational (((1 : ℚ) : ℝ) * (0 : ℝ)) :=
    dummy_assumed (r := (1 : ℚ)) (by norm_num) (x := (0 : ℝ)) (by simp [Irrational])
  simpa [Irrational] using hzero
