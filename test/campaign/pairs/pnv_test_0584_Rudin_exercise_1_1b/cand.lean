import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {x : ℝ} (hx : Irrational x) (r : ℚ) (hr : r ≠ 0) : Irrational (r * x) := sorry
