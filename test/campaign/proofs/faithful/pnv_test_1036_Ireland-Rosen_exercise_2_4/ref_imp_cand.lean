import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_4_assumed {a : ℤ} (ha : a ≠ 0)
  (hf : f_a = λ n m : ℕ => Int.gcd (a^(2^n) + 1) (a^(2^m)+1)) {n m : ℕ}
  (hnm : n > m) :
  (Odd a → f_a n m = 2) ∧ (Even a → f_a n m = 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a : ℤ} (ha : a ≠ 0) (n m : ℕ) (h : n > m) : gcd (a^(2^n) + 1) (a^(2^m) + 1) = if a % 2 = 0 then 1 else 2 := by
  have hparity := exercise_2_4_assumed ha rfl h
  by_cases heven : a % 2 = 0
  · rw [if_pos heven]
    rw [← Int.coe_gcd]
    exact_mod_cast hparity.2 ((Int.even_iff).mpr heven)
  · rw [if_neg heven]
    rw [← Int.coe_gcd]
    exact_mod_cast hparity.1 ((Int.not_even_iff_odd).mp (by
      intro haeven
      exact heven ((Int.even_iff).mp haeven)))
