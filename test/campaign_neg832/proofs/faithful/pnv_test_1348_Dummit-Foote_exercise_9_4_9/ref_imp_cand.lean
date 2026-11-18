import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_9_4_9_assumed :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {R : Type*} [CommRing R] [IsDomain R] [Algebra ℤ R] (hR : ∀ a b : R, Irreducible (a * b) → Irreducible a ∨ Irreducible b) (hsqrt2 : IsIntegral ℤ (sqrt2 : R)) : Irreducible (Polynomial.map (algebraMap ℤ R) (Polynomial.X^2 - C (sqrt2))) := by
  -- not proved: the candidate has an auto-implicit integer `sqrt2` and is not a specialization of the reference statement
  sorry
