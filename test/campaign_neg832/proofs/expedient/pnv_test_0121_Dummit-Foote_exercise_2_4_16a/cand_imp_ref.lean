import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {H : Subgroup G} (hH : H ≠ ⊤) : ∃ (M : Subgroup G), M ≠ ⊤ ∧ ∀ (M' : Subgroup G), M' ≠ ⊤ → M' ≠ M → M' ≤ H → M' = H ∨ M' = ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  let S : Set (Subgroup G) := {K | K ≠ ⊤}
  obtain ⟨M, hHM, hM⟩ := (Set.toFinite S).exists_le_maximal (show H ∈ S from hH)
  refine ⟨M, hM.1, ?_, hHM⟩
  intro K hMK
  by_cases hK : K = ⊤
  · exact Or.inr hK
  · exact Or.inl (le_antisymm (hM.2 hK hMK) hMK)
