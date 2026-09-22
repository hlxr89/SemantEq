import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy (S : Set (Set ℝ)) (hS : S = {s | ∃ (a b : ℚ), a < b ∧ s = {x : ℝ | a < x ∧ x < b}}) : TopologicalSpace.IsTopologicalBasis S := sorry
