import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy (U : Set (ℝ × ℝ)) : (∃ (a b c d : ℚ), a < b ∧ c < d ∧ U = Set.Ioo (a : ℝ) b ×ˢ Set.Ioo (c : ℝ) d) → ∀ (x : ℝ × ℝ), ∃ (V : Set (ℝ × ℝ)), (∃ (a b c d : ℚ), a < b ∧ c < d ∧ V = Set.Ioo (a : ℝ) b ×ˢ Set.Ioo (c : ℝ) d) ∧ x ∈ V ∧ V ⊆ U := sorry
