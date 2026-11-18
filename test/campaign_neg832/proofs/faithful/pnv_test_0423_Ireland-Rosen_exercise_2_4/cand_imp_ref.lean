import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (n m : ℕ) (a : ℤ) (ha : a ≠ 0) (hn : n > m) : gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = if a % 2 = 0 then 1 else 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4 {a : ℤ} (ha : a ≠ 0)
  (hf : f_a = λ n m : ℕ => Int.gcd (a^(2^n) + 1) (a^(2^m)+1)) {n m : ℕ}
  (hnm : n > m) :
  (Odd a → f_a n m = 2) ∧ (Even a → f_a n m = 1) := by
  constructor
  · intro haodd
    rw [hf]
    have hmod : a % 2 ≠ 0 := by
      rw [← Int.not_even_iff_odd, even_iff_two_dvd,
        Int.dvd_iff_emod_eq_zero] at haodd
      exact haodd
    have hc := dummy_assumed n m a ha hnm
    rw [if_neg hmod] at hc
    have hc' : (↑(Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)) : ℤ) = 2 := by
      simpa only [Int.coe_gcd] using hc
    exact_mod_cast hc'
  · intro haeven
    rw [hf]
    have hmod : a % 2 = 0 :=
      Int.dvd_iff_emod_eq_zero.mp (even_iff_two_dvd.mp haeven)
    have hc := dummy_assumed n m a ha hnm
    rw [if_pos hmod] at hc
    have hc' : (↑(Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)) : ℤ) = 1 := by
      simpa only [Int.coe_gcd] using hc
    exact_mod_cast hc'
