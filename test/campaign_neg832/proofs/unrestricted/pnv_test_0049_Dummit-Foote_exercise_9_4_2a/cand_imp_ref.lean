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
  let f : Polynomial ℤ := X ^ 4 - 4 * X ^ 3 + 6
  have hf : f = X ^ 4 - 4 * X ^ 3 + 6 := rfl
  have hm : f.Monic := by
    dsimp [f]
    monicity <;> norm_num
  have hnone := dummy_assumed f hf
  rw [irreducible_iff]
  constructor
  · rw [hm.isUnit_iff]
    intro hunit
    have hcoeff := congrArg (fun g : Polynomial ℤ ↦ g.coeff 0) hunit
    norm_num [f] at hcoeff
  · intro p q hpq
    by_contra hunits
    rw [not_or] at hunits
    apply hnone
    refine ⟨p, q, hpq.symm, ?_, ?_⟩
    · exact Polynomial.degree_pos_of_not_isUnit_of_dvd_monic hm hunits.1 ⟨q, hpq⟩
    · apply Polynomial.degree_pos_of_not_isUnit_of_dvd_monic hm hunits.2
      refine ⟨p, ?_⟩
      rw [mul_comm]
      exact hpq
