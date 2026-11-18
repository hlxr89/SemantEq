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
  intro hxy
  have hn := dummy_assumed (r := y⁻¹) (inv_ne_zero h) (fun hirr ↦ hirr hxy)
  apply hn
  simpa only [Rat.cast_inv, mul_comm x (y : ℝ), ← mul_assoc,
    inv_mul_cancel₀ (Rat.cast_ne_zero.mpr h : (y : ℝ) ≠ 0), one_mul] using hx
