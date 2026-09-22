import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
open MvPolynomial

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_9_4_11_refs_assumed :
  Irreducible ((MvPolynomial.X 0)^2 + (MvPolynomial.X 1)^2 - 1 : MvPolynomial (Fin 2) ℚ) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_11 :
    Irreducible (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) :=
  by
    exact exercise_9_4_11_refs_assumed
