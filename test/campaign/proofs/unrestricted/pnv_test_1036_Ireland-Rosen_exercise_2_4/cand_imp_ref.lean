import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℤ} (ha : a ≠ 0) (n m : ℕ) (h : n > m) : gcd (a^(2^n) + 1) (a^(2^m) + 1) = if a % 2 = 0 then 1 else 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4 {a : ℤ} (ha : a ≠ 0)
  (hf : f_a = λ n m : ℕ => Int.gcd (a^(2^n) + 1) (a^(2^m)+1)) {n m : ℕ}
  (hnm : n > m) :
  (Odd a → f_a n m = 2) ∧ (Even a → f_a n m = 1) := by
  constructor
  · intro hodd
    rw [hf]
    have hc := dummy_assumed ha n m hnm
    have hmod : a % 2 = 1 := Int.odd_iff.mp hodd
    have hne : a % 2 ≠ 0 := by omega
    rw [if_neg hne] at hc
    have hc' : (Int.gcd (a^(2^n) + 1) (a^(2^m) + 1) : ℤ) = 2 := by
      rw [Int.coe_gcd]
      exact hc
    exact_mod_cast hc'
  · intro heven
    rw [hf]
    have hc := dummy_assumed ha n m hnm
    rw [if_pos (Int.even_iff.mp heven)] at hc
    have hc' : (Int.gcd (a^(2^n) + 1) (a^(2^m) + 1) : ℤ) = 1 := by
      rw [Int.coe_gcd]
      exact hc
    exact_mod_cast hc'
