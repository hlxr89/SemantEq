import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1_3_alt_assumed (n : ℤ) :
  ∀ (a b c : ℤ), a+(b+c) ≡ (a+b)+c [ZMOD n] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_3 (n : ℤ) :
  ∀ (a b c : ℤ), (a+b)+c ≡ a+(b+c) [ZMOD n] := by
  intro a b c
  exact (exercise_1_1_3_alt_assumed n a b c).symm
