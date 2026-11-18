import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : Polynomial ℚ) (hf : f.degree = 3) (hf0 : f.coeff 0 = 2) (hf1 : f.coeff 1 = 3) (hf2 : f.coeff 2 = 1) : Irreducible f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6_2 : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  let f : Polynomial ℚ := C (-6) * X^3 + X^2 + C 3 * X + C 2
  have hf : f.degree = 3 := by
    apply degree_eq_of_le_of_coeff_ne_zero
    · rw [degree_le_iff_coeff_zero]
      intro m hm
      norm_num at hm
      simp [f, coeff_X, coeff_X_pow, coeff_C, show m ≠ 3 by omega,
        show m ≠ 2 by omega, show 1 ≠ m by omega, show m ≠ 0 by omega]
    · norm_num [f, coeff_X]
  have hf0 : f.coeff 0 = 2 := by
    simp [f, coeff_X]
  have hf1 : f.coeff 1 = 3 := by
    simp [f]
  have hf2 : f.coeff 2 = 1 := by
    simp [f, coeff_X]
  have hi := dummy_assumed f hf hf0 hf1 hf2
  have hfac : f = (X - C 1) * (C (-6) * X^2 - C 5 * X - C 2) := by
    dsimp [f]
    simp [C_ofNat]
    ring
  rw [hfac] at hi
  rcases hi.isUnit_or_isUnit rfl with h | h
  · exact ((not_isUnit_X_sub_C (1 : ℚ)) h).elim
  · have hd : (C (-6) * X^2 - C 5 * X - C 2 : Polynomial ℚ).degree = 2 := by
      apply degree_eq_of_le_of_coeff_ne_zero
      · rw [degree_le_iff_coeff_zero]
        intro m hm
        norm_num at hm
        simp [coeff_X, coeff_X_pow, coeff_C, show m ≠ 2 by omega,
          show 1 ≠ m by omega, show m ≠ 0 by omega]
      · norm_num [coeff_X]
    exact (Polynomial.not_isUnit_of_degree_pos _ (by rw [hd]; norm_num) h).elim
