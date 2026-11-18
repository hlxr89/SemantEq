import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {H : Subgroup G} (hH : H ≠ ⊤) : ∃ M : Subgroup G, M ≠ ⊤ ∧ H ≤ M ∧ ∀ K : Subgroup G, H ≤ K → K ≤ M → K = M ∨ K = ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  obtain ⟨M, hM, hHM, -⟩ := dummy_assumed hH
  obtain ⟨N, hMN, hNmax⟩ :=
    Finite.exists_le_maximal (α := Subgroup G) (p := fun K => K ≠ ⊤) hM
  refine ⟨N, hNmax.1, ?_, hHM.trans hMN⟩
  intro K hNK
  by_cases hK : K = ⊤
  · exact Or.inr hK
  · exact Or.inl (le_antisymm (hNmax.2 hK hNK) hNK)
