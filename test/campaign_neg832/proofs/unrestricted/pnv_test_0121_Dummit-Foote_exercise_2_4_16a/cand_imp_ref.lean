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
  classical
  obtain ⟨M, hHM, hmax⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G => K ≠ ⊤) hH
  refine ⟨M, (maximal_iff.mp hmax).1, ?_, hHM⟩
  intro K hMK
  by_cases hK : K = ⊤
  · exact Or.inr hK
  · exact Or.inl ((maximal_iff.mp hmax).2 hK hMK).symm
