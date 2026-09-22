import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1b_assumed
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( Irrational x ) -> Irrational ( x * y ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {r : ℚ} {x : ℝ} (hr : r ≠ 0) (hx : Irrational x) : Irrational (r * x) := by
  rw [mul_comm]
  exact exercise_1_1b_assumed x r hr hx
