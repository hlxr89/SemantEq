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
  have h := dummy_assumed (a := a) ha n m hnm
  constructor
  · intro ha_odd
    rw [hf]
    have h_int := h.resolve_left (by
      intro h_one
      have hn_even : Even (a ^ (2 ^ n) + 1) :=
        Odd.add_odd ha_odd.pow (by norm_num)
      have hm_even : Even (a ^ (2 ^ m) + 1) :=
        Odd.add_odd ha_odd.pow (by norm_num)
      have h_two_dvd : (2 : ℤ) ∣ gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) :=
        GCDMonoid.dvd_gcd (even_iff_two_dvd.mp hn_even) (even_iff_two_dvd.mp hm_even)
      rw [h_one] at h_two_dvd
      norm_num at h_two_dvd)
    have h_cast : (Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) : ℤ) = 2 := by
      rw [Int.coe_gcd]
      exact h_int
    exact_mod_cast h_cast
  · intro ha_even
    rw [hf]
    have h_int := h.resolve_right (by
      intro h_two
      have hn_odd : Odd (a ^ (2 ^ n) + 1) :=
        (ha_even.pow_of_ne_zero (Nat.two_pow_pos n).ne').add_one
      have h_two_dvd : (2 : ℤ) ∣ a ^ (2 ^ n) + 1 := by
        have hgcd_dvd := GCDMonoid.gcd_dvd_left
          (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)
        rw [h_two] at hgcd_dvd
        exact hgcd_dvd
      exact (Int.not_even_iff_odd.mpr hn_odd) (even_iff_two_dvd.mpr h_two_dvd))
    have h_cast : (Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) : ℤ) = 1 := by
      rw [Int.coe_gcd]
      exact h_int
    exact_mod_cast h_cast
