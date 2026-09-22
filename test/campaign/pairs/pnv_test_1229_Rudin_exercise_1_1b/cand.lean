import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (x : ℝ) (hx : Irrational x) (q : ℚ) (hq : q ≠ 0) : Irrational (q * x) := sorry
