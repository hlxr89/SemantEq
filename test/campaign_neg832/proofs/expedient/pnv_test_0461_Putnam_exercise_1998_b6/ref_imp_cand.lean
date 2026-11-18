import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b c : ℤ) (h : ∃ n : ℤ, (n : ℝ)^3 + (a * n^2) + (b * n) + c ≠ (n : ℝ)) : ∃ n : ℤ, 0 < n ∧ (n : ℝ)^3 + (a * n^2) + (b * n) + c ≠ (n : ℝ) := by
  by_cases h1 : ((1 : ℝ)^3 + (a * (1 : ℤ)^2) + (b * (1 : ℤ)) + c) ≠ (1 : ℝ)
  · exact ⟨1, by norm_num, by simpa using h1⟩
  by_cases h2 : ((2 : ℝ)^3 + (a * (2 : ℤ)^2) + (b * (2 : ℤ)) + c) ≠ (2 : ℝ)
  · exact ⟨2, by norm_num, by simpa using h2⟩
  by_cases h3 : ((3 : ℝ)^3 + (a * (3 : ℤ)^2) + (b * (3 : ℤ)) + c) ≠ (3 : ℝ)
  · exact ⟨3, by norm_num, by simpa using h3⟩
  refine ⟨4, by norm_num, ?_⟩
  intro h4
  push_neg at h1 h2 h3
  norm_num at h1 h2 h3 h4
  nlinarith
