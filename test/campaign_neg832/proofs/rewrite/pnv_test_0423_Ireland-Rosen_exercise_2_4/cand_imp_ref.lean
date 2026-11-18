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
  have hvalue := dummy_assumed n m a ha hnm
  constructor
  · intro hodd
    have h : a % 2 ≠ 0 := by
      intro hz
      have heven : Even a := even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero hz)
      exact (Int.not_even_iff_odd.mpr hodd) heven
    rw [if_neg h] at hvalue
    apply (Nat.cast_inj (R := ℤ)).mp
    rw [Int.coe_gcd]
    exact hvalue
  · intro heven
    have h : a % 2 = 0 := Int.emod_eq_zero_of_dvd (even_iff_two_dvd.mp heven)
    rw [if_pos h] at hvalue
    apply (Nat.cast_inj (R := ℤ)).mp
    rw [Int.coe_gcd]
    exact hvalue
