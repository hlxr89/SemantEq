import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α] : IsTopologicalBasis { s : Set α | ∃ a b : α, a < b ∧ s = Ioo a b } := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_8a :
  IsTopologicalBasis {S : Set ℝ | ∃ a b : ℚ, a < b ∧ S = Ioo ↑a ↑b} := by
  refine IsTopologicalBasis.of_hasBasis_nhds fun x => ?_
  refine (dummy_assumed (α := ℝ)).nhds_hasBasis.to_hasBasis ?_ ?_
  · intro s hs
    rcases hs with ⟨⟨a, b, hab, rfl⟩, hax, hxb⟩
    obtain ⟨q, haq, hqx⟩ := exists_rat_btwn hax
    obtain ⟨p, hxp, hpb⟩ := exists_rat_btwn hxb
    refine ⟨Ioo (q : ℝ) p, ?_, Ioo_subset_Ioo haq.le hpb.le⟩
    exact ⟨⟨q, p, Rat.cast_lt.mp (hqx.trans hxp), rfl⟩, hqx, hxp⟩
  · intro s hs
    rcases hs with ⟨⟨q, p, hqp, rfl⟩, hx⟩
    exact ⟨Ioo (q : ℝ) p, ⟨⟨q, p, Rat.cast_lt.mpr hqp, rfl⟩, hx⟩, Subset.rfl⟩
