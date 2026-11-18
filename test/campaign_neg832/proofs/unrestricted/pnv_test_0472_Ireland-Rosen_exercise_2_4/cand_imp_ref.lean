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
  have h_cases_nat :
      Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 ∨
        Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2 := by
    rcases dummy_assumed ha n m hnm with h_one | h_two
    · left
      have h_coe :
          (Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) : ℤ) = 1 := by
        rw [Int.coe_gcd]
        exact h_one
      exact_mod_cast h_coe
    · right
      have h_coe :
          (Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) : ℤ) = 2 := by
        rw [Int.coe_gcd]
        exact h_two
      exact_mod_cast h_coe
  constructor
  · intro ha_odd
    rw [hf]
    rcases h_cases_nat with h_one | h_two
    · have h_left : (2 : ℤ) ∣ a ^ (2 ^ n) + 1 := (ha_odd.pow.add_one).two_dvd
      have h_right : (2 : ℤ) ∣ a ^ (2 ^ m) + 1 := (ha_odd.pow.add_one).two_dvd
      have h_bad : (2 : ℤ) ∣ 1 :=
        (Int.gcd_eq_one_iff.mp h_one) 2 h_left h_right
      norm_num at h_bad
    · exact h_two
  · intro ha_even
    rw [hf]
    rcases h_cases_nat with h_one | h_two
    · exact h_one
    · have h_power_even : Even (a ^ (2 ^ n)) :=
        ha_even.pow_of_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      have h_sum_odd : Odd (a ^ (2 ^ n) + 1) := h_power_even.add_one
      have h_two_dvd : (2 : ℤ) ∣ a ^ (2 ^ n) + 1 := by
        have hd := Int.gcd_dvd_left (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)
        rw [h_two] at hd
        exact hd
      rcases h_sum_odd with ⟨k, hk⟩
      rcases h_two_dvd with ⟨j, hj⟩
      omega
