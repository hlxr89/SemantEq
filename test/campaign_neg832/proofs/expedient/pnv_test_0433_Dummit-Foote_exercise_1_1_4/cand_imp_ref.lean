import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) (a b c : ℕ) : ((a * b) % n) * (c % n) % n = a * (b * c) % n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by
  exact mul_assoc a b c
