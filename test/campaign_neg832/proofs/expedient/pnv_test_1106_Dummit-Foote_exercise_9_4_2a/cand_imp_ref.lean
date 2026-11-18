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
  let P : Ideal ℤ := Ideal.span {2}
  have hp : P.IsPrime := by
    exact (Ideal.span_singleton_prime (by norm_num)).2 (by norm_num)
  have hm : (X^4 - 4*X^3 + 6 : Polynomial ℤ).Monic := by
    monicity <;> norm_num
  have hd : (X^4 - 4*X^3 + 6 : Polynomial ℤ).degree = 4 := by
    compute_degree
    · norm_num
    · change 4 ≤ (4 : ℕ)
      omega
    · change 3 ≤ (4 : ℕ)
      omega
  apply irreducible_of_eisenstein_criterion (P := P)
  · exact hp
  · exact hm.leadingCoeff_notMem hp.ne_top
  · intro n hn
    rw [hd] at hn
    have hn' : n < 4 := by exact_mod_cast hn
    have : n ≤ 3 := by omega
    interval_cases n <;> simp [P, Ideal.mem_span_singleton]
  · rw [hd]
    norm_num
  · rw [show (X^4 - 4*X^3 + 6 : Polynomial ℤ).coeff 0 = 6 by norm_num]
    dsimp [P]
    rw [pow_two, Ideal.span_singleton_mul_span_singleton]
    simp [Ideal.mem_span_singleton]
  · exact hm.isPrimitive
