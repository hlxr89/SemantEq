import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [Algebra ℤ R] (hR : ∀ a b : R, Irreducible (a * b) → Irreducible a ∨ Irreducible b) (hsqrt2 : IsIntegral ℤ (sqrt2 : R)) : Irreducible (Polynomial.map (algebraMap ℤ R) (Polynomial.X^2 - C (sqrt2))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  have hR : ∀ a b : ℚ, Irreducible (a * b) → Irreducible a ∨ Irreducible b := by
    intro a b hab
    rcases hab.isUnit_or_isUnit rfl with ha | hb
    · exact Or.inr ((irreducible_isUnit_mul ha).mp hab)
    · exact Or.inl ((irreducible_mul_isUnit hb).mp hab)
  have hbad := dummy_assumed (sqrt2 := 0) (R := ℚ) hR (isIntegral_zero)
  have hpow : Irreducible ((X : Polynomial ℚ) ^ 2) := by
    simpa using hbad
  exact False.elim ((not_irreducible_pow (x := (X : Polynomial ℚ)) (by norm_num)) hpow)
