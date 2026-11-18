import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {α : Type*} [TopologicalSpace α] : TopologicalSpace.IsTopologicalBasis {s : Set ℝ | ∃ (a b : ℚ), (a : ℝ) < b ∧ s = Set.Ioo (a : ℝ) (b : ℝ)} := sorry
