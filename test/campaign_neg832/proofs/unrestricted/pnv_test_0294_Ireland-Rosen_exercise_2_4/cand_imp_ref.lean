import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℤ} (ha : a ≠ 0) (n m : ℕ) (hnm : n > m) : if a % 2 = 0 then gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2 else gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4 {a : ℤ} (ha : a ≠ 0)
  (hf : f_a = λ n m : ℕ => Int.gcd (a^(2^n) + 1) (a^(2^m)+1)) {n m : ℕ}
  (hnm : n > m) :
  (Odd a → f_a n m = 2) ∧ (Even a → f_a n m = 1) := by
  have h := dummy_assumed ha n m hnm
  by_cases he : a % 2 = 0
  · simp only [if_pos he] at h
    have hd : (2 : ℤ) ∣ a ^ (2 ^ n) + 1 := by
      rw [← h]
      exact Int.gcd_dvd_left _ _
    have hea : Even a := Int.even_iff.mpr he
    have hodd : Odd (a ^ (2 ^ n) + 1) := by
      apply Even.add_one
      have hnpos : 0 < 2 ^ n := by positivity
      rw [show 2 ^ n = (2 ^ n - 1) + 1 by omega, pow_succ]
      exact hea.mul_left _
    exact False.elim ((Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd))
  · have ho : a % 2 = 1 := (Int.emod_two_eq_zero_or_one a).resolve_left he
    simp only [if_neg he] at h
    have hnatgcd : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 := by
      exact_mod_cast (show (Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) : ℤ) = 1 by
        rw [Int.coe_gcd, h])
    have hcoprime := Int.gcd_eq_one_iff.mp hnatgcd
    have haodd : Odd a := Int.odd_iff.mpr ho
    have hd₁ : (2 : ℤ) ∣ a ^ (2 ^ n) + 1 := by
      apply even_iff_two_dvd.mp
      exact haodd.pow.add_one
    have hd₂ : (2 : ℤ) ∣ a ^ (2 ^ m) + 1 := by
      apply even_iff_two_dvd.mp
      exact haodd.pow.add_one
    have : (2 : ℤ) ∣ 1 := hcoprime 2 hd₁ hd₂
    norm_num at this
