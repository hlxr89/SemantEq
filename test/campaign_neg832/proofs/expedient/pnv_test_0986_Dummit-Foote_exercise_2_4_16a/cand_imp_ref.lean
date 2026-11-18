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
  let S : Set (Subgroup G) := {K | H ≤ K ∧ K ≠ ⊤}
  obtain ⟨M, hM⟩ := Set.toFinite S |>.exists_maximal ⟨H, le_rfl, hH⟩
  refine ⟨M, hM.1.2, ?_, hM.1.1⟩
  intro K hMK
  by_cases hK : K = ⊤
  · exact Or.inr hK
  · left
    exact le_antisymm (hM.2 ⟨hM.1.1.trans hMK, hK⟩ hMK) hMK
