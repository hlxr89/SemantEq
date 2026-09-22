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
  obtain ⟨n, hn, hnsqrt⟩ := exercise_1998_b6_assumed a b c
  have hnat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
  refine ⟨n.toNat, ?_⟩
  rintro ⟨m, hm⟩
  apply hnsqrt
  refine ⟨|m|, ?_⟩
  rw [hnat] at hm
  have hm' : (m : ℝ) ^ 2 = (n : ℝ) ^ 3 + (a : ℝ) * (n : ℝ) ^ 2 +
      (b : ℝ) * (n : ℝ) + (c : ℝ) := by
    exact_mod_cast hm
  rw [← hm']
  norm_num [Real.sqrt_sq_eq_abs]
