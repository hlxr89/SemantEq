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
  have hparts := exercise_2_4_assumed (a := a) ha
    (f_a := λ n m : ℕ => Int.gcd (a^(2^n) + 1) (a^(2^m)+1)) rfl h
  split
  next heven =>
    rw [← Int.coe_gcd]
    exact_mod_cast hparts.2 (Int.even_iff.mpr heven)
  next hnot_even =>
    have hodd : Odd a :=
      (Int.even_or_odd a).resolve_left (fun heven => hnot_even (Int.even_iff.mp heven))
    rw [← Int.coe_gcd]
    exact_mod_cast hparts.1 hodd
