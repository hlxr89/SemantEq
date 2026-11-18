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
theorem dummy (G : Type*) [Group G] [Finite G] : ∃ (p : Nat) (hp : p.Prime) (P : Sylow p G), (P : Subgroup G).Normal := by
  -- not proved: the antecedent only concerns groups of order 351, while the goal concerns every finite group
  sorry
