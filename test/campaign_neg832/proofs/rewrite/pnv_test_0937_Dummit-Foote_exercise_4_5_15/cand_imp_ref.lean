import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 351) : ∃ p : ℕ, ∃ P : Sylow p G, P.toSubgroup.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_15 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  -- not proved: the candidate's Sylow witness does not imply that p is prime or divides card G
  sorry
