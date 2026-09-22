import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b c : ℤ) : ∃ n : ℕ, 0 < n ∧ ¬(∃ m : ℤ, m^2 = n^3 + a * n^2 + b * n + c) := by
  obtain ⟨n, hn, hno⟩ := exercise_1998_b6_assumed a b c
  have hn' : 0 < n.toNat := by
    omega -- non-rewrite step
  refine ⟨n.toNat, hn', ?_⟩
  rintro ⟨m, hm⟩
  apply hno
  refine ⟨|m|, ?_⟩
  rw [Int.cast_abs, ← Real.sqrt_sq_eq_abs]
  congr 1
  rw [← Int.toNat_of_nonneg (le_of_lt hn)]
  exact_mod_cast hm.symm
