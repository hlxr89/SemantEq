import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_5_15_assumed {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 351) : ∃ p : ℕ, ∃ P : Sylow p G, P.toSubgroup.Normal := by
  obtain ⟨p, P, _, _, hP⟩ := exercise_4_5_15_assumed hG
  exact ⟨p, P, hP⟩
