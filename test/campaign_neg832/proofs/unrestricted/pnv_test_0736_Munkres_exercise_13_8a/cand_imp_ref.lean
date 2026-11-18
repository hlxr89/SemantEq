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
  · rintro V ⟨a, b, hab, rfl⟩
    exact isOpen_Ioo
  · intro x U hx hU
    obtain ⟨a, b, hab, hxI, hIU⟩ := dummy_assumed x U hU hx
    exact ⟨Ioo (a : ℝ) b, ⟨a, b, hab, rfl⟩, hxI, hIU⟩
