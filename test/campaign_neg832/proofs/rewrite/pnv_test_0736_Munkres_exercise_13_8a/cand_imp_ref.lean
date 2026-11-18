import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (x : ℝ) (U : Set ℝ) (hU : IsOpen U) (hx : x ∈ U) : ∃ (a b : ℚ), a < b ∧ x ∈ Set.Ioo (a : ℝ) b ∧ Set.Ioo (a : ℝ) b ⊆ U := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_8a :
  IsTopologicalBasis {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo ↑a ↑b} := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro S hS
    rcases hS with ⟨a, b, hab, rfl⟩
    exact isOpen_Ioo
  · intro x U hx hU
    rcases dummy_assumed x U hU hx with ⟨a, b, hab, hxIoo, hIooU⟩
    exact ⟨Ioo (a : ℝ) b, ⟨a, b, hab, rfl⟩, hxIoo, hIooU⟩
