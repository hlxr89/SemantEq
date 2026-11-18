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
  have hparts := exercise_2_4_assumed (a := a) ha rfl (n := n) (m := m) hn
  by_cases h : a % 2 = 0
  · rw [if_pos h]
    have hnat := hparts.2 (even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero h))
    rw [← Int.coe_gcd]
    exact congrArg (fun k : ℕ => (k : ℤ)) hnat
  · rw [if_neg h]
    have hodd : Odd a := Int.not_even_iff_odd.mp (by
      intro heven
      exact h (Int.emod_eq_zero_of_dvd (even_iff_two_dvd.mp heven)))
    have hnat := hparts.1 hodd
    rw [← Int.coe_gcd]
    exact congrArg (fun k : ℕ => (k : ℤ)) hnat
