import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (f : R[X]) (h : f = X^4 - 4 * X^3 + 6) : ¬ ∃ (g : R[X]) (h : R[X]), f = g * (X - 1) * (X - 2) * (X - 3) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  let f : Polynomial ℤ := X^4 - 4*X^3 + 6
  have hantecedent := dummy_assumed (R := ℤ) f rfl
  have hdeg : f.natDegree = 4 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      cases N <;> simp_all [f, Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_mul, Polynomial.coeff_X_pow]
      omega
    · norm_num [f, Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_mul, Polynomial.coeff_X_pow]
  have hmonic : f.Monic := by
    rw [Polynomial.Monic.def]
    rw [Polynomial.leadingCoeff, hdeg]
    norm_num [f, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_mul, Polynomial.coeff_X_pow]
  let P : Ideal ℤ := Ideal.span {2}
  have hP : P.IsPrime := by
    dsimp [P]
    exact (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).2 (by norm_num)
  have heis : f.IsEisensteinAt P := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [P] using hmonic.leadingCoeff_notMem hP.ne_top
    · intro n hn
      rw [hdeg] at hn
      interval_cases n <;> norm_num [f, P, Ideal.mem_span_singleton,
        Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_X_pow]
    · rw [show P ^ 2 = Ideal.span {(4 : ℤ)} by simp [P, Ideal.span_singleton_pow]]
      norm_num [f, Ideal.mem_span_singleton, Polynomial.coeff_sub,
        Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X_pow]
  simpa [f] using heis.irreducible hP hmonic.isPrimitive (by omega)
