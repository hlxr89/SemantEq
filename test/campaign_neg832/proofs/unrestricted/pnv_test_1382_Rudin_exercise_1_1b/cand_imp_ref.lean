import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {r x : ℝ} (hr : r ≠ 0) (hx : Irrational x) : Irrational (r * x) := by
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
  simpa [mul_comm] using dummy_assumed (r := (y : ℝ)) (x := x) hy hx
