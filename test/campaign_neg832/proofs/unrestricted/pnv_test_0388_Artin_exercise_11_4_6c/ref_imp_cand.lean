import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_11_4_6c_assumed : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (p : ℕ) [hp : Fact p.Prime] : Irreducible (X^3 - C 9 : Polynomial (ZMod p)) := by
  -- not proved: false for p = 3, where X^3 - C 9 = X^3 is reducible
  sorry
