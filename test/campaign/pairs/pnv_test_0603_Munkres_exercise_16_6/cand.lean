import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy (U : Set (Set (ℝ × ℝ))) : U = { s | ∃ (a b c d : ℚ), a < b ∧ c < d ∧ s = Set.Ioo (a : ℝ) b ×ˢ Set.Ioo (c : ℝ) d } → TopologicalSpace.IsTopologicalBasis U := sorry
