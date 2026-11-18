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
  intro hx
  rintro ⟨q, hq⟩
  apply hx
  refine ⟨q / y, ?_⟩
  rw [Rat.cast_div]
  apply (div_eq_iff (Rat.cast_ne_zero.mpr h)).2
  exact hq
