import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [Group G] [Finite G] (H : Subgroup G) [Subgroup.Normal H] (hH : H ≠ ⊤) : ∃ M : Subgroup G, H ≤ M ∧ ∀ N : Subgroup G, H ≤ N → N = M ∨ N = ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  have hcore : H.normalCore ≠ ⊤ := by
    intro htop
    apply hH
    apply top_unique
    rw [← htop]
    exact H.normalCore_le
  letI : H.normalCore.Normal := H.normalCore_normal
  obtain ⟨M, hcoreM, hmax⟩ := dummy_assumed H.normalCore hcore
  have hHM : H = M := (hmax H H.normalCore_le).resolve_right hH
  refine ⟨H, hH, ?_, le_rfl⟩
  intro K hHK
  rcases hmax K (H.normalCore_le.trans hHK) with hKM | hKtop
  · exact Or.inl (hKM.trans hHM.symm)
  · exact Or.inr hKtop
