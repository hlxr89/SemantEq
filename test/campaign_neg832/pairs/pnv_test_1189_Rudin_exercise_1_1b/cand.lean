import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {x r : ℝ} (hx : Irrational x) (hr : r ≠ 0) : Irrational (r * x) := sorry
