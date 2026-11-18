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
  have hreal := dummy_assumed (α := ℝ)
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro s ⟨a, b, hab, rfl⟩
    rw [hreal.isOpen_iff]
    intro x hx
    exact ⟨Ioo (a : ℝ) (b : ℝ), ⟨a, b, by exact_mod_cast hab, rfl⟩, hx, subset_rfl⟩
  · intro x u hxu hu
    obtain ⟨t, ⟨a, b, hab, rfl⟩, hxt, htu⟩ := (hreal.isOpen_iff.mp hu) x hxu
    obtain ⟨qa, haqa, haqx⟩ := exists_rat_btwn hxt.1
    obtain ⟨qb, hxqb, hqbb⟩ := exists_rat_btwn hxt.2
    refine ⟨Ioo (qa : ℝ) (qb : ℝ), ⟨qa, qb, ?_, rfl⟩, ⟨haqx, hxqb⟩, ?_⟩
    · exact_mod_cast lt_trans haqx hxqb
    · intro y hy
      exact htu ⟨lt_trans haqa hy.1, lt_trans hy.2 hqbb⟩
