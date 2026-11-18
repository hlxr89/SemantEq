import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {n : ℕ} {x : EuclideanSpace ℚ (Fin n)} (h : ∑ i, x i = 0): ∃ (y : EuclideanSpace ℚ (Fin n)), y ≠ 0 := sorry
