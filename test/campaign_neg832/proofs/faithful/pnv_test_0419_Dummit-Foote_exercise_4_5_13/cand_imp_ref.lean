import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] : Fintype.card G = 56 → ∃ (p : ℕ)(H : Sylow p G), H.Normal := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  -- not proved: the candidate permits the vacuous p = 1 Sylow witness and supplies neither primality nor divisibility
  sorry
