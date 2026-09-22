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
    · have h_one_nat : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 :=
        Int.ofNat_inj.mp (by simpa only [Int.coe_gcd, Nat.cast_ofNat] using h_one)
      have hn_even : Even (a ^ (2 ^ n) + 1) := ha_odd.pow.add_one
      have hm_even : Even (a ^ (2 ^ m) + 1) := ha_odd.pow.add_one
      have h_two_dvd_gcd : 2 ∣ Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) :=
        Int.dvd_gcd (even_iff_two_dvd.mp hn_even) (even_iff_two_dvd.mp hm_even)
      have h_two_dvd_one : (2 : ℕ) ∣ 1 := by
        rw [h_one_nat] at h_two_dvd_gcd
        exact h_two_dvd_gcd
      exact (Nat.not_even_one (even_iff_two_dvd.mpr h_two_dvd_one)).elim
    · exact Int.ofNat_inj.mp (by
        simpa only [Int.coe_gcd, Nat.cast_ofNat] using h_two)
  · intro ha_even
    rcases h with h_one | h_two
    · exact Int.ofNat_inj.mp (by
        simpa only [Int.coe_gcd, Nat.cast_ofNat] using h_one)
    · have h_two_nat : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2 :=
        Int.ofNat_inj.mp (by simpa only [Int.coe_gcd, Nat.cast_ofNat] using h_two)
      have h_exp_ne : (2 ^ n : ℕ) ≠ 0 :=
        pow_ne_zero n (OfNat.zero_ne_ofNat 2).symm
      have hn_odd : Odd (a ^ (2 ^ n) + 1) :=
        (ha_even.pow_of_ne_zero h_exp_ne).add_one
      have h_gcd_dvd := Int.gcd_dvd_left (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)
      rw [h_two_nat] at h_gcd_dvd
      exact ((Int.not_even_iff_odd.mpr hn_odd) (even_iff_two_dvd.mpr h_gcd_dvd)).elim
