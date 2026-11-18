import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_11_4_6c_assumed : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (x : ℤ) : Irreducible (X^3 - C (↑x)) := by
  -- not proved: false for x = 0, since X^3 is a nontrivial power
  sorry
