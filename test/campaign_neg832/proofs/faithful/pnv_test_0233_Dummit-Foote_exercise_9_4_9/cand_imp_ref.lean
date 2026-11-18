import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra ℚ R] [IsScalarTower ℚ R R] : Irreducible ((Polynomial.X ^ 2 - 2 : Polynomial ℚ).map (algebraMap ℚ R)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  -- not proved: using the false universal antecedent would require the forbidden ex-falso route, not a re-expression bridge
  sorry
