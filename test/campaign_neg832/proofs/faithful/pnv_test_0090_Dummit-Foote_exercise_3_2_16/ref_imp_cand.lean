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
  have h := exercise_3_2_16_assumed p hp.out (a : ℤ)
  rw [Nat.modEq_iff_dvd]
  rw [Int.modEq_iff_dvd] at h
  simpa using h
