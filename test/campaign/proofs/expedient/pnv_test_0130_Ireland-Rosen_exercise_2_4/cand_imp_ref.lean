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
  have h := dummy_assumed ha n m hnm
  rw [hf]
  constructor
  · intro haodd
    rcases h with h | h
    · exfalso
      have hNat : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 := by
        exact_mod_cast (show ((Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) : ℕ) : ℤ) = 1 by
          simpa only [Int.coe_gcd] using h)
      have hn' : Even (a ^ (2 ^ n) + 1) := haodd.pow.add_one
      have hm' : Even (a ^ (2 ^ m) + 1) := haodd.pow.add_one
      have hn2 : (2 : ℤ) ∣ a ^ (2 ^ n) + 1 := by
        rcases hn' with ⟨k, hk⟩
        use k
        omega
      have hm2 : (2 : ℤ) ∣ a ^ (2 ^ m) + 1 := by
        rcases hm' with ⟨k, hk⟩
        use k
        omega
      have := Int.gcd_eq_one_iff.mp hNat 2 hn2 hm2
      norm_num at this
    · exact_mod_cast (show ((Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) : ℕ) : ℤ) = 2 by
        simpa only [Int.coe_gcd] using h)
  · intro haeven
    rcases h with h | h
    · exact_mod_cast (show ((Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) : ℕ) : ℤ) = 1 by
        simpa only [Int.coe_gcd] using h)
    · exfalso
      have hNat : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2 := by
        exact_mod_cast (show ((Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) : ℕ) : ℤ) = 2 by
          simpa only [Int.coe_gcd] using h)
      have hx : Odd (a ^ (2 ^ n) + 1) := (Int.even_pow.mpr ⟨haeven, by positivity⟩).add_one
      have hd := Int.gcd_dvd_left (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)
      rw [hNat] at hd
      rcases hx with ⟨k, hk⟩
      rcases hd with ⟨j, hj⟩
      norm_num at hj
      omega
