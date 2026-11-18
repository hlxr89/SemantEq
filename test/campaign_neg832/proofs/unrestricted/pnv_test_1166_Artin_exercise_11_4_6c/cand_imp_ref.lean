import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] [CharP F 31] {x : F} (h : x^3 - 9 ≠ 0) : Irreducible (x^3 - 9) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hne : (0 : ZMod 31)^3 - 9 ≠ 0 := by
    change (-9 : ZMod 31) ≠ 0
    decide
  have hirr : Irreducible ((0 : ZMod 31)^3 - 9) :=
    dummy_assumed (F := ZMod 31) (x := 0) hne
  have hu : IsUnit ((0 : ZMod 31)^3 - 9) := isUnit_iff_ne_zero.mpr hne
  exact (hirr.not_isUnit hu).elim
