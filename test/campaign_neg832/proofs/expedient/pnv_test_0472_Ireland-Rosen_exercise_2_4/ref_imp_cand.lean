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
theorem dummy {a : ℤ} (ha : a ≠ 0) (n m : ℕ) (hn : n > m): gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 ∨ gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2 := by
  have h := exercise_2_4_assumed ha (f_a := fun n m => Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1)) rfl hn
  rcases Int.even_or_odd a with ha | ha
  · left
    rw [← Int.coe_gcd]
    exact_mod_cast h.2 ha
  · right
    rw [← Int.coe_gcd]
    exact_mod_cast h.1 ha
