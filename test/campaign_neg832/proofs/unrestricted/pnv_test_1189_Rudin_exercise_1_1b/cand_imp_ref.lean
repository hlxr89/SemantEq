import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {x r : ℝ} (hx : Irrational x) (hr : r ≠ 0) : Irrational (r * x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1b
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( Irrational x ) -> Irrational ( x * y ) := by
  intro hx
  have hy : (y : ℝ) ≠ 0 := by
    exact_mod_cast h
  simpa [mul_comm] using (dummy_assumed hx hy)
