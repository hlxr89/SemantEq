import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_13_8a_assumed :
  IsTopologicalBasis {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo ↑a ↑b} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : TopologicalSpace.IsTopologicalBasis (Set.range fun p : ℚ × ℚ => Ioo p.1 p.2) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨p, rfl⟩
    exact isOpen_Ioo
  · intro x U hx hU
    obtain ⟨a, b, hxab, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
    exact ⟨Ioo a b, ⟨(a, b), rfl⟩, hxab, hab⟩
