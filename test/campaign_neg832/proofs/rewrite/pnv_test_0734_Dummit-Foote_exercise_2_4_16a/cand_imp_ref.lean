import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] [Fintype G] (H : Subgroup G) (hH : H ≠ ⊤) : ∃ M : Subgroup G, M ≠ ⊤ ∧ ∀ N : Subgroup G, N ≠ ⊤ → N ≠ M → M ≤ N := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  obtain ⟨L, hL, hleast⟩ := dummy_assumed G H hH
  have hLH : L ≤ H := by
    by_cases hHL : H = L
    · rw [hHL]
    · exact hleast H hH hHL
  let S : Set (Subgroup G) := {K | K ≠ ⊤ ∧ H ≤ K ∧ L ≤ K}
  have hHS : H ∈ S := ⟨hH, le_rfl, hLH⟩
  obtain ⟨M, hHM, hMmax⟩ := (Set.toFinite S).exists_le_maximal hHS -- non-rewrite step
  refine ⟨M, hMmax.1.1, ?_, hHM⟩
  intro K hMK
  by_cases hK : K = ⊤
  · exact Or.inr hK
  · exact Or.inl (le_antisymm (hMmax.2 ⟨hK, hHM.trans hMK, (hLH.trans hHM).trans hMK⟩ hMK) hMK)
