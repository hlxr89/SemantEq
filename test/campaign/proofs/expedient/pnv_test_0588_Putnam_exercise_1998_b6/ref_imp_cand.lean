import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b c : ℤ) : ∃ n : ℕ, 0 < n ∧ ¬ ∃ k : ℤ, k^2 = n^3 + a * n^2 + b * n + c := by
  obtain ⟨n, hn, hnsqrt⟩ := exercise_1998_b6_assumed a b c
  lift n to ℕ using le_of_lt hn with n
  refine ⟨n, by exact_mod_cast hn, ?_⟩
  rintro ⟨k, hk⟩
  apply hnsqrt
  have hp : 0 ≤ (n : ℤ)^3 + a * (n : ℤ)^2 + b * (n : ℤ) + c := by
    rw [← hk]
    positivity
  refine ⟨|k|, ?_⟩
  have hkR : (k : ℝ)^2 = (↑(n : ℤ) : ℝ)^3 + (a : ℝ) * (↑(n : ℤ) : ℝ)^2 +
      (b : ℝ) * (↑(n : ℤ) : ℝ) + c := by exact_mod_cast hk
  rw [← hkR]
  simpa using (Real.sqrt_sq_eq_abs (k : ℝ))
