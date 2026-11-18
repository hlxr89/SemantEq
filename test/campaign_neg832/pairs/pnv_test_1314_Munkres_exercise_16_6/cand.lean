import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy : ∃ B : Set (Set (ℝ × ℝ)), B.Countable ∧ (∀ U, IsOpen U ↔ ∃ S ⊆ B, U = ⋃₀ S) := sorry
