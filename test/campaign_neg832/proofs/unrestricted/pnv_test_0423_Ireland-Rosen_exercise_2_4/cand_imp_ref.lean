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
  rw [hf]
  have h := dummy_assumed n m a ha hnm
  constructor
  · intro hodd
    have hne : a % 2 ≠ 0 := by
      rw [Int.odd_iff] at hodd
      omega
    have hg : gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = (2 : ℤ) := by
      rw [h]
      simp [hne]
    have hg' : (↑(Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)) : ℤ) = 2 := by
      rw [Int.coe_gcd]
      exact hg
    exact_mod_cast hg'
  · intro heven
    have heq : a % 2 = 0 := by
      rw [Int.even_iff] at heven
      exact heven
    have hg : gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = (1 : ℤ) := by
      rw [h]
      simp [heq]
    have hg' : (↑(Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)) : ℤ) = 1 := by
      rw [Int.coe_gcd]
      exact hg
    exact_mod_cast hg'
