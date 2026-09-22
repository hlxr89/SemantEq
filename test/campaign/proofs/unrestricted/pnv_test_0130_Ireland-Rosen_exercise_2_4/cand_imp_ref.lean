import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℤ} (ha : a ≠ 0) (n m : ℕ) (hnm : n > m) : (gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 ∨ gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2) := by
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
    rcases h with h_one | h_two
    · have hdiv_left : (2 : ℤ) ∣ a ^ (2 ^ n) + 1 :=
        even_iff_two_dvd.mp (ha_odd.pow.add_one)
      have hdiv_right : (2 : ℤ) ∣ a ^ (2 ^ m) + 1 :=
        even_iff_two_dvd.mp (ha_odd.pow.add_one)
      have hdiv_gcd : 2 ∣ Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) :=
        Int.dvd_gcd hdiv_left hdiv_right
      rw [← Int.coe_gcd] at h_one
      have h_one_nat : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 := by
        exact_mod_cast h_one
      rw [h_one_nat] at hdiv_gcd
      norm_num at hdiv_gcd
    · rw [← Int.coe_gcd] at h_two
      exact_mod_cast h_two
  · intro ha_even
    rcases h with h_one | h_two
    · rw [← Int.coe_gcd] at h_one
      exact_mod_cast h_one
    · have hpow_even : Even (a ^ (2 ^ n)) :=
        ha_even.pow_of_ne_zero (by positivity)
      have hodd_left : Odd (a ^ (2 ^ n) + 1) := hpow_even.add_one
      have hdiv_left : (2 : ℤ) ∣ a ^ (2 ^ n) + 1 := by
        rw [← Int.coe_gcd] at h_two
        rw [← h_two]
        exact Int.gcd_dvd_left _ _
      have heven_left : Even (a ^ (2 ^ n) + 1) := even_iff_two_dvd.mpr hdiv_left
      rcases hodd_left with ⟨k, hk⟩
      rcases heven_left with ⟨l, hl⟩
      omega
