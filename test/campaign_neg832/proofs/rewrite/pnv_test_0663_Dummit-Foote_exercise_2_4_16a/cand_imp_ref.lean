import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : H ≠ ⊤) : ∃ (M : Subgroup G) (hM : M ≠ ⊤), H ≤ M ∧ ∀ (K : Subgroup G), H ≤ K → M = K ∨ K = ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  obtain ⟨M, hM, hHM, hmax⟩ := dummy_assumed hH
  refine ⟨M, hM, ?_, hHM⟩
  intro K hMK
  rcases hmax K (hHM.trans hMK) with hKM | hKtop
  · exact Or.inl hKM.symm
  · exact Or.inr hKtop
