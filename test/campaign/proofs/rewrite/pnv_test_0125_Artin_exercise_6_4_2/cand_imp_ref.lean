import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] [Fintype G] {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hcard : Fintype.card G = p * q) : ¬IsSimpleGroup G := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_6_4_2 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p*q) :
  IsSimpleGroup G → false := by
  simpa only [Bool.false_eq_true] using
    dummy_assumed G (Nat.prime_iff.mpr hp) (Nat.prime_iff.mpr hq) hG
