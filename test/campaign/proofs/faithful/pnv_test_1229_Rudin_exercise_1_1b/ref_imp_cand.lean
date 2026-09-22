import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1b_assumed
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( Irrational x ) -> Irrational ( x * y ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (x : ℝ) (hx : Irrational x) (q : ℚ) (hq : q ≠ 0) : Irrational (q * x) := by
  simpa [mul_comm] using exercise_1_1b_assumed x q hq hx
