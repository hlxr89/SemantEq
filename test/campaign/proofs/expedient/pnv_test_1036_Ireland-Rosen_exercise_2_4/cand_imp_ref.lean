import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℤ} (ha : a ≠ 0) (n m : ℕ) (h : n > m) : gcd (a^(2^n) + 1) (a^(2^m) + 1) = if a % 2 = 0 then 1 else 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4 {a : ℤ} (ha : a ≠ 0)
  (hf : f_a = λ n m : ℕ => Int.gcd (a^(2^n) + 1) (a^(2^m)+1)) {n m : ℕ}
  (hnm : n > m) :
  (Odd a → f_a n m = 2) ∧ (Even a → f_a n m = 1) := by
  subst f_a
  constructor
  · intro ho
    have hd := dummy_assumed ha n m hnm
    rw [if_neg (fun hp => Int.not_odd_iff_even.mpr (Int.even_iff.mpr hp) ho)] at hd
    rw [← Int.coe_gcd] at hd
    change Int.gcd (a^(2^n) + 1) (a^(2^m)+1) = 2
    exact_mod_cast hd
  · intro he
    have hd := dummy_assumed ha n m hnm
    rw [if_pos (Int.even_iff.mp he)] at hd
    rw [← Int.coe_gcd] at hd
    change Int.gcd (a^(2^n) + 1) (a^(2^m)+1) = 1
    exact_mod_cast hd
