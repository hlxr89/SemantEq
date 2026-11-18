import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℤ} (ha : a ≠ 0) (n m : ℕ) (hn : n > m): gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 ∨ gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4 {a : ℤ} (ha : a ≠ 0)
  (hf : f_a = λ n m : ℕ => Int.gcd (a^(2^n) + 1) (a^(2^m)+1)) {n m : ℕ}
  (hnm : n > m) :
  (Odd a → f_a n m = 2) ∧ (Even a → f_a n m = 1) := by
  rw [hf]
  have h := dummy_assumed ha n m hnm
  constructor
  · intro ha_odd
    obtain h_one | h_two := h
    · rw [← Int.coe_gcd] at h_one
      have h_one' : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 := by
        exact_mod_cast h_one
      have hx_even : Even (a ^ (2 ^ n) + 1) :=
        Odd.add_odd (ha_odd.pow) odd_one
      have hy_even : Even (a ^ (2 ^ m) + 1) :=
        Odd.add_odd (ha_odd.pow) odd_one
      have h_dvd : 2 ∣ Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) :=
        Int.dvd_gcd (even_iff_two_dvd.mp hx_even) (even_iff_two_dvd.mp hy_even)
      rw [h_one'] at h_dvd
      exact (Nat.not_succ_le_self 1 (Nat.le_of_dvd Nat.zero_lt_one h_dvd)).elim -- non-rewrite step
    · rw [← Int.coe_gcd] at h_two
      exact_mod_cast h_two
  · intro ha_even
    obtain h_one | h_two := h
    · rw [← Int.coe_gcd] at h_one
      exact_mod_cast h_one
    · rw [← Int.coe_gcd] at h_two
      have h_two' : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2 := by
        exact_mod_cast h_two
      have hx_odd : Odd (a ^ (2 ^ n) + 1) :=
        Even.add_odd (ha_even.pow_of_ne_zero (Nat.two_pow_pos n).ne') odd_one
      have h_dvd : (2 : ℤ) ∣ a ^ (2 ^ n) + 1 := by
        have hd := Int.gcd_dvd_left (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)
        rw [h_two'] at hd
        exact hd
      exact ((Int.not_even_iff_odd.mpr hx_odd) (even_iff_two_dvd.mpr h_dvd)).elim -- non-rewrite step
