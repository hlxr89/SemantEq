import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [Ring R] [IsDomain R] (f : R[X]) (h : f = X ^ 4 - 4 * X ^ 3 + 6) : ¬ ∃ (p q : R[X]), p * q = f ∧ 0 < degree p ∧ 0 < degree q := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have hnf := dummy_assumed (R := ℤ) (X ^ 4 - 4 * X ^ 3 + 6) rfl
  have hm : Monic (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ) := by
    monicity
    · simpa only [mul_one, zero_add] using
        le_trans (le_max_left 4 3) (le_max_left (max 4 3) 0)
    · simpa only [mul_one, zero_add] using
        le_trans (le_max_right 4 3) (le_max_left (max 4 3) 0)
  rw [hm.irreducible_iff_natDegree]
  constructor
  · intro heq
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 0) heq
    simp only [coeff_add, coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte,
      coeff_ofNat_mul, mul_zero, sub_self, coeff_ofNat_zero, zero_add, coeff_one_zero,
      OfNat.ofNat_ne_one] at hc
  · intro p q _ _ hpq
    have hdegrees : ¬ (0 < degree p ∧ 0 < degree q) := by
      intro h
      exact hnf ⟨p, q, hpq, h.1, h.2⟩
    exact (not_and_or.mp hdegrees).imp
      (fun hp => Nat.eq_zero_of_not_pos (fun h => hp (natDegree_pos_iff_degree_pos.mp h)))
      (fun hq => Nat.eq_zero_of_not_pos (fun h => hq (natDegree_pos_iff_degree_pos.mp h)))
