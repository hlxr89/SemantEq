import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_2_16_assumed (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (p : ℕ) [Fact p.Prime] (a : ℕ) : a ^ p ≡ a [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  simpa only [Int.natCast_pow] using
    exercise_3_2_16_assumed p (Fact.out) (a : ℤ)
