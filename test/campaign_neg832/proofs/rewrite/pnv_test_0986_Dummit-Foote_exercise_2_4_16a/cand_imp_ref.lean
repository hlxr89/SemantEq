import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {H : Subgroup G} (hH : H ≠ ⊤) : ∃ M : Subgroup G, M ≠ ⊤ ∧ (∀ K : Subgroup G, H ≤ K → M ≤ K → K = M ∨ K = ⊤) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  -- The candidate witness need not contain H, so finite maximality is the
  -- non-rewrite step needed to recover a witness of the reference shape.
  have _htransport := dummy_assumed hH
  obtain ⟨M, hHM, hmax⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G ↦ K ≠ ⊤) hH
  refine ⟨M, hmax.1, ?_, hHM⟩
  intro K hMK
  by_cases hK : K = ⊤
  · exact Or.inr hK
  · exact Or.inl (le_antisymm (hmax.2 hK hMK) hMK)
