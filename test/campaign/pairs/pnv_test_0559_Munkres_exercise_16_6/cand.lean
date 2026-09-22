import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy : ∃ (B : Set (Set (ℝ × ℝ))), B.Countable ∧ TopologicalSpace.IsTopologicalBasis B ∧ ∀ U ∈ B, ∃ (a b c d : ℚ), a < b ∧ c < d ∧ U = Set.Ioo (a : ℝ) b ×ˢ Set.Ioo (c : ℝ) d := sorry
