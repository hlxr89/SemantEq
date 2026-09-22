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
  obtain ⟨hOdd, hEven⟩ := exercise_2_4_assumed ha rfl h
  by_cases haEven : Even a
  · rw [if_pos (Int.even_iff.mp haEven), ← Int.coe_gcd]
    exact congrArg (fun x : ℕ => (x : ℤ)) (hEven haEven)
  · rw [if_neg (fun haMod => haEven (Int.even_iff.mpr haMod)), ← Int.coe_gcd]
    exact congrArg (fun x : ℕ => (x : ℤ)) (hOdd (Int.not_even_iff_odd.mp haEven))
