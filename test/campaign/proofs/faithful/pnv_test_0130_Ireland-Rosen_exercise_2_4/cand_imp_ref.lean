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
  subst f_a
  constructor
  · intro ha_odd
    have hc :
        Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 ∨
          Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2 := by
      rcases dummy_assumed ha n m hnm with h | h
      · left
        rw [← Int.coe_gcd] at h
        exact_mod_cast h
      · right
        rw [← Int.coe_gcd] at h
        exact_mod_cast h
    have hn_even : Even (a ^ (2 ^ n) + 1) := ha_odd.pow.add_one
    have hm_even : Even (a ^ (2 ^ m) + 1) := ha_odd.pow.add_one
    have hgcd_two_dvd : 2 ∣ Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) :=
      Int.dvd_gcd (even_iff_two_dvd.mp hn_even) (even_iff_two_dvd.mp hm_even)
    have hgcd_ne_one : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) ≠ 1 := by
      intro hgcd_one
      rw [hgcd_one] at hgcd_two_dvd
      norm_num at hgcd_two_dvd
    exact hc.resolve_left hgcd_ne_one
  · intro ha_even
    have hc :
        Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 ∨
          Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2 := by
      rcases dummy_assumed ha n m hnm with h | h
      · left
        rw [← Int.coe_gcd] at h
        exact_mod_cast h
      · right
        rw [← Int.coe_gcd] at h
        exact_mod_cast h
    have hn_odd : Odd (a ^ (2 ^ n) + 1) :=
      (Int.even_pow.mpr ⟨ha_even, by positivity⟩).add_one
    have hgcd_ne_two : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) ≠ 2 := by
      intro hgcd_two
      have htwo_dvd := Int.gcd_dvd_left (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)
      rw [hgcd_two] at htwo_dvd
      exact (Int.not_even_iff_odd.mpr hn_odd) (even_iff_two_dvd.mpr htwo_dvd)
    exact hc.resolve_right hgcd_ne_two
