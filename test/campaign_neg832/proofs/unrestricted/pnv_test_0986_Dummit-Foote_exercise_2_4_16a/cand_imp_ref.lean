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
  have _hcand := dummy_assumed hH
  let p : Subgroup G → Prop := fun K ↦ H ≤ K ∧ K ≠ ⊤
  have hpH : p H := ⟨le_rfl, hH⟩
  obtain ⟨M, hHM, hMp, hMmax⟩ := Finite.exists_le_maximal hpH
  refine ⟨M, hMp.2, ?_, hHM⟩
  intro K hMK
  by_cases hKtop : K = ⊤
  · exact Or.inr hKtop
  · left
    apply le_antisymm
    · exact hMmax ⟨hHM.trans hMK, hKtop⟩ hMK
    · exact hMK
