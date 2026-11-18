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
theorem dummy (n : ℕ) (a b c : ℤ) : (a * b)%n * c %n = a * (b * c) %n := by
  calc
    (a * b)%n * c %n = (a * b) * c %n := by
      rw [Int.mul_emod (a * b) c n, Int.mul_emod ((a * b) % n) c n,
        Int.emod_emod]
    _ = a * (b * c) %n := by rw [mul_assoc]
