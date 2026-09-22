import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (x : ℝ) (hx : x ≠ 0) : ¬∃ (y : ℝ), y ≠ 0 ∧ x * y = 0 := sorry
