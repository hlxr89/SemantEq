import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_11_4_6c_assumed : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {F : Type*} [Field F] [CharP F 31] (p : Polynomial F) (h : p = X^3 - 9) : Irreducible p := by
  -- not proved: irreducibility over ZMod 31 does not imply irreducibility over every characteristic-31 extension field
  sorry
