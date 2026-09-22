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
theorem dummy {a : ℤ} (ha : a ≠ 0) (n m : ℕ) (hnm : n > m) : (gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 ∨ gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2) := by
  have h := exercise_2_4_assumed (a := a) ha rfl hnm
  rcases Int.even_or_odd a with he | ho
  · left
    simpa only [← Int.coe_gcd] using congrArg (fun k : ℕ => (k : ℤ)) (h.2 he)
  · right
    simpa only [← Int.coe_gcd] using congrArg (fun k : ℕ => (k : ℤ)) (h.1 ho)
