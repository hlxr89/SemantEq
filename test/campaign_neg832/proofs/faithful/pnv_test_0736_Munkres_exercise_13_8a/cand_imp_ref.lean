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
  apply IsTopologicalBasis.of_hasBasis_nhds
  intro x
  refine Filter.HasBasis.mk ?_
  intro U
  constructor
  · intro hU
    obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
    obtain ⟨a, b, hab, hxab, habV⟩ := dummy_assumed x V hVopen hxV
    refine ⟨Ioo (a : ℝ) b, ?_, habV.trans hVU⟩
    exact ⟨⟨a, b, hab, rfl⟩, hxab⟩
  · rintro ⟨S, ⟨hS, hxS⟩, hSU⟩
    rcases hS with ⟨a, b, hab, rfl⟩
    exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hxS) hSU
