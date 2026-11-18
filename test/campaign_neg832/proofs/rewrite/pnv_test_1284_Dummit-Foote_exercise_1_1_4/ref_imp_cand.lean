import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1_4_assumed (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (n : ℕ) (a b c : ℤ) : (a * b) * c = a * (b * c) := by
  have h := exercise_1_1_4_assumed 0 (a : ZMod 0) (b : ZMod 0) (c : ZMod 0)
  exact_mod_cast h
