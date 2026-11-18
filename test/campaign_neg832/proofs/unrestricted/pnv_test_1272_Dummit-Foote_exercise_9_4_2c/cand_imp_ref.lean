import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℤ[X]) (hp1 : p.degree = 4) (hp2 : p.eval (-1) = 1) (hp3 : p.eval 1 = 1) : Irreducible p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  have hbad : Irreducible (X ^ 4 : ℤ[X]) := by
    apply dummy_assumed
    · simp [Polynomial.degree_pow]
    · norm_num
    · norm_num
  have hu : IsUnit (X ^ 2 : ℤ[X]) := by
    rcases hbad.isUnit_or_isUnit (by ring : (X ^ 4 : ℤ[X]) = X ^ 2 * X ^ 2) with h | h
    · exact h
    · exact h
  rcases Polynomial.isUnit_iff.mp hu with ⟨r, hr, heq⟩
  have hc := congrArg (fun q : ℤ[X] => q.coeff 2) heq
  change (C r : ℤ[X]).coeff 2 = (X ^ 2 : ℤ[X]).coeff 2 at hc
  rw [Polynomial.coeff_C, Polynomial.coeff_X_pow] at hc
  norm_num at hc
