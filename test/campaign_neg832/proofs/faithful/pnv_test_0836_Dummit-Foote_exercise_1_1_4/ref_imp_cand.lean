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
theorem dummy (n : ℕ) (a b c : ℕ) : (a * b) % n * (c % n) % n = a * b * c % n := by
  have h := exercise_1_1_4_assumed n (a : ZMod n) (b : ZMod n) (c : ZMod n)
  simpa [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod] using congrArg ZMod.val h
