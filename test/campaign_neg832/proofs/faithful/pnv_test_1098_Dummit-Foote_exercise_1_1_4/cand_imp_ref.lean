import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) (a b c : ℤ) : (a * b)%n * c %n = a * (b * c) %n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by
  have h := dummy_assumed n (ZMod.cast a) (ZMod.cast b) (ZMod.cast c)
  have hc := congrArg (fun x : ℤ => (x : ZMod n)) h
  simpa only [Int.cast_mul, ZMod.intCast_mod, ZMod.intCast_zmod_cast] using hc
