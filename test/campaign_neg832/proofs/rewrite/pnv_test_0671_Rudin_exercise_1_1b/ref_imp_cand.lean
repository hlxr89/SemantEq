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
  intro hrx
  apply hx
  have h := exercise_1_1b_assumed (r * x) r⁻¹ (inv_ne_zero hr) hrx
  simpa only [Rat.cast_inv, mul_comm (r : ℝ) x, mul_assoc,
    mul_inv_cancel₀ (Rat.cast_ne_zero.mpr hr : (r : ℝ) ≠ 0), mul_one] using h
