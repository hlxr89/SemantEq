import Mathlib
open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {r : ℚ} (hr : r ≠ 0) {x : ℝ} (hx : ¬ Irrational x) : ¬ Irrational (r * x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1b
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( Irrational x ) -> Irrational ( x * y ) := by
  intro hx
  by_contra hxy
  have hback := dummy_assumed (r := y⁻¹) (inv_ne_zero h) (x := x * (y : ℝ)) hxy
  exact hback (by simpa [mul_assoc, mul_left_comm, mul_comm, h] using hx)
