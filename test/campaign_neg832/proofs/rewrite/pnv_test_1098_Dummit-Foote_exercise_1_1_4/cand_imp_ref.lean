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
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b
  obtain ⟨c, rfl⟩ := ZMod.intCast_surjective c
  rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_mul, ← Int.cast_mul]
  apply (ZMod.intCast_eq_intCast_iff' (a * b * c) (a * (b * c)) n).mpr
  have h := dummy_assumed n a b c
  simpa only [Int.mul_emod, Int.emod_emod] using h
