import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℤ} (ha : a ≠ 0) (n m : ℕ) (hnm : n > m) : Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = if Even a then 2 else 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_4 {a : ℤ} (ha : a ≠ 0)
  (hf : f_a = λ n m : ℕ => Int.gcd (a^(2^n) + 1) (a^(2^m)+1)) {n m : ℕ}
  (hnm : n > m) :
  (Odd a → f_a n m = 2) ∧ (Even a → f_a n m = 1) := by
  have hbad := dummy_assumed (a := 2) (by norm_num) 1 0 (by norm_num)
  norm_num at hbad
