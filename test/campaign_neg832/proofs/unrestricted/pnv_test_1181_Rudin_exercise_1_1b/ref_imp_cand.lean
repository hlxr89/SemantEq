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
theorem dummy {r : ℚ} (hr : r ≠ 0) {x : ℝ} (hx : ¬ Irrational x) : Irrational (r * x) := by
  -- not proved: false when r = 1 and x = 0, whereas the antecedent is true
  sorry
