import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b c : ℤ) : ∃ (n : ℕ), ¬ ∃ (m : ℤ), m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
  obtain ⟨n, hn, h⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.toNat, ?_⟩
  rintro ⟨m, hm⟩
  apply h
  refine ⟨|m|, ?_⟩
  have hn' : (n.toNat : ℤ) = n := by omega
  rw [Int.cast_abs, ← Real.sqrt_sq_eq_abs]
  congr 1
  norm_cast
  simpa [hn'] using hm.symm
