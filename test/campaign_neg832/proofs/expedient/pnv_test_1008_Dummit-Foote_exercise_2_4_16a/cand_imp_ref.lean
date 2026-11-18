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
  classical
  let p : Subgroup G → Prop := fun K => H ≤ K ∧ K ≠ ⊤
  have hp : p H := ⟨le_rfl, hH⟩
  obtain ⟨M, hHM, hM⟩ := Finite.exists_le_maximal (p := p) hp
  refine ⟨M, hM.1.2, ?_, hHM⟩
  intro K hMK
  by_cases hK : K = ⊤
  · exact Or.inr hK
  · exact Or.inl (le_antisymm (hM.2 ⟨hHM.trans hMK, hK⟩ hMK) hMK)
