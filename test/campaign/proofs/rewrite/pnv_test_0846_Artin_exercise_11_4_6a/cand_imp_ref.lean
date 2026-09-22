import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : Irreducible (X ^ 2 + X + 1 : Polynomial (ZMod 2)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_4_6a {F : Type*} [Field F] [Fintype F] (hF : card F = 2) :
  Irreducible (X ^ 2 + X + 1 : Polynomial F) := by
  let e : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hF
  have h := dummy_assumed.map (Polynomial.mapEquiv e)
  simpa only [Polynomial.mapEquiv_apply, map_add, map_pow, map_one,
    Polynomial.map_X] using h
