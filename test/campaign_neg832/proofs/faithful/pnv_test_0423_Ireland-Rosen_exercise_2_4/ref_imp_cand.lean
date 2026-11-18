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
theorem dummy (n m : ℕ) (a : ℤ) (ha : a ≠ 0) (hn : n > m) : gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = if a % 2 = 0 then 1 else 2 := by
  have h := exercise_2_4_assumed (a := a) (f_a := fun n m : ℕ =>
    Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)) ha rfl hn
  by_cases hmod : a % 2 = 0
  · rw [if_pos hmod, ← Int.coe_gcd]
    exact_mod_cast h.2 (even_iff_two_dvd.mpr
      (Int.dvd_iff_emod_eq_zero.mpr hmod))
  · rw [if_neg hmod, ← Int.coe_gcd]
    have haodd : Odd a := by
      rw [← Int.not_even_iff_odd, even_iff_two_dvd,
        Int.dvd_iff_emod_eq_zero]
      exact hmod
    exact_mod_cast h.1 haodd
