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
theorem dummy {r : ℚ} (hr : r ≠ 0) {x : ℝ} (hx : ¬ Irrational x) : ¬ Irrational (r * x) := by
  intro hirr
  apply hx
  have hback := exercise_1_1b_assumed ((r : ℝ) * x) r⁻¹ (inv_ne_zero hr) hirr
  simpa [mul_assoc, mul_left_comm, mul_comm, hr] using hback
