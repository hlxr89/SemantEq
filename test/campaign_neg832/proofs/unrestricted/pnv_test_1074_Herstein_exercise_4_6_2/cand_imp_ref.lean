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
    apply Polynomial.degree_eq_of_le_of_coeff_ne_zero
    · rw [Polynomial.degree_le_iff_coeff_zero]
      intro m hm
      have hm' : 3 < m := by exact_mod_cast hm
      have h3 : m ≠ 3 := by omega
      have h2 : m ≠ 2 := by omega
      have h1 : m ≠ 1 := by omega
      have h0 : m ≠ 0 := by omega
      simp [f, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
        h3, h2, Ne.symm h1, h0]
    · norm_num [f, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  have hf0 : f.coeff 0 = 2 := by
    norm_num [f, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  have hf1 : f.coeff 1 = 3 := by
    norm_num [f, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  have hf2 : f.coeff 2 = 1 := by
    norm_num [f, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  have hi : Irreducible f := dummy_assumed f hf hf0 hf1 hf2
  have hr : f.IsRoot 1 := by norm_num [f, Polynomial.IsRoot]
  have hd := Polynomial.degree_eq_one_of_irreducible_of_root hi hr
  rw [hf] at hd
  norm_num at hd
