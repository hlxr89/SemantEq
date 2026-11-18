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
  rcases dummy_assumed ha n m hnm with h | h
  · rw [← Int.coe_gcd] at h
    norm_cast at h
    refine ⟨?_, fun _ => h⟩
    intro ha
    have hn : Even (a ^ (2 ^ n) + 1) := ha.pow.add_one
    have hm : Even (a ^ (2 ^ m) + 1) := ha.pow.add_one
    have hd : 2 ∣ Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) :=
      Int.dvd_gcd (even_iff_two_dvd.mp hn) (even_iff_two_dvd.mp hm)
    rw [h] at hd
    norm_num at hd
  · rw [← Int.coe_gcd] at h
    norm_cast at h
    refine ⟨fun _ => h, ?_⟩
    intro ha
    have hm : Even (a ^ (2 ^ m)) := ha.pow_of_ne_zero (by positivity)
    have ho : Odd (a ^ (2 ^ m) + 1) := hm.add_one
    have hd := Int.gcd_dvd_right (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)
    rw [h] at hd
    rcases hd with ⟨k, hk⟩
    rcases ho with ⟨l, hl⟩
    omega
