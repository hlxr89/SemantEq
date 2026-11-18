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
  have hbot : (⊥ : Subgroup G) ≠ ⊤ := by
    intro h
    apply hH
    apply top_unique
    rw [← h]
    exact bot_le
  obtain ⟨M, _, hmax⟩ := dummy_assumed (G := G) (⊥ : Subgroup G) hbot
  have hHM : H = M := (hmax H bot_le).resolve_right hH
  refine ⟨M, ?_, ?_, ?_⟩
  · rw [← hHM]
    exact hH
  · intro K _
    exact hmax K bot_le
  · rw [hHM]
