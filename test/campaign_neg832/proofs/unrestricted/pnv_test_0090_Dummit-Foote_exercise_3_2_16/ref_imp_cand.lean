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
theorem dummy {a : ℕ} {p : ℕ} [hp : Fact (Nat.Prime p)] : a ^ p ≡ a [MOD p] := by
  apply Int.natCast_modEq_iff.mp
  simpa only [Nat.cast_pow] using
    (exercise_3_2_16_assumed p hp.out (a : ℤ))
