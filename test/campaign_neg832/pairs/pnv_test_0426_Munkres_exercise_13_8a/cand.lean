import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy : ∀ U : Set ℝ, IsOpen U ↔ ∀ x ∈ U, ∃ a b : ℚ, a < b ∧ a < x ∧ x < b := sorry
