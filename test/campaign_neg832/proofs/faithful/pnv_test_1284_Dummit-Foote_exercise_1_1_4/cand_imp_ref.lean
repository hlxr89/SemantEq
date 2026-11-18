import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n : ℕ) (a b c : ℤ) : (a * b) * c = a * (b * c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_4 (n : ℕ) (a b c : ZMod n) :
  (a * b) * c = a * (b * c) := by
  cases n with
  | zero =>
      exact dummy_assumed 0 a b c
  | succ n =>
      have h := dummy_assumed (n + 1) (a.val : ℤ) (b.val : ℤ) (c.val : ℤ)
      have h' := congrArg (fun x : ℤ => (x : ZMod (n + 1))) h
      simpa only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] using h'
