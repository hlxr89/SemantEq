import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {H : Subgroup G} (hH : H ≠ ⊤) : ∃ M : Subgroup G, M ≠ ⊤ ∧ (∀ K : Subgroup G, H ≤ K → K = M ∨ K = ⊤) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  obtain ⟨M, hM, hmax⟩ := dummy_assumed hH
  have hHM : H ≤ M := by
    rcases hmax H le_rfl with hEq | hTop
    · exact hEq.le
    · exact (hH hTop).elim
  refine ⟨M, hM, ?_, hHM⟩
  intro K hMK
  exact hmax K (hHM.trans hMK)
