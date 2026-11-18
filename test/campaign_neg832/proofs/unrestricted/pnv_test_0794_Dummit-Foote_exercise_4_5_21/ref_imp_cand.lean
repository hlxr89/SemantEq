import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_5_21_assumed {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] (h : Nat.card G = 2907) : ∃ H : Subgroup G, H.Normal ∧ H ≠ ⊥ := by
  have hns : ¬ Subsingleton G := by
    intro hs
    have hone : Nat.card G = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hs, inferInstance⟩
    omega
  letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hns
  exact ⟨⊤, Subgroup.normal_top, top_ne_bot⟩
