import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (x : ℤ) : Irreducible (X^3 - C (↑x)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  exfalso
  apply not_irreducible_pow (x := (X : Polynomial ℤ)) (n := 3) (by decide)
  simpa using dummy_assumed 0
