import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy : TopologicalSpace.IsTopologicalBasis {s : Set ℝ | ∃ (a b : ℚ), a < b ∧ s = Set.Ioo (a : ℝ) (b : ℝ)} := sorry
