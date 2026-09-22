import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (r : ℚ) (hr : r ≠ 0) {x : ℝ} (hx : Irrational x) : Irrational (r * x) := sorry
