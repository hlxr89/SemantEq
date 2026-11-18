import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {r x : ℝ} (hr : r ≠ 0) (hx : Irrational x) : Irrational (r * x) := sorry
