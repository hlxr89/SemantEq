import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a b c : ℤ} : ∃ (n : ℕ) (H : 0 < n), ¬(n : ℝ) ^ 3 + a * n ^ 2 + b * n + c = 0 := by
  by_cases h1 : (1 : ℝ) ^ 3 + a * (1 : ℕ) ^ 2 + b * (1 : ℕ) + c = 0
  · by_cases h2 : (2 : ℝ) ^ 3 + a * (2 : ℕ) ^ 2 + b * (2 : ℕ) + c = 0
    · by_cases h3 : (3 : ℝ) ^ 3 + a * (3 : ℕ) ^ 2 + b * (3 : ℕ) + c = 0
      · refine ⟨4, by norm_num, ?_⟩
        intro h4
        norm_num at h1 h2 h3 h4
        linarith
      · refine ⟨3, by norm_num, ?_⟩
        simpa using h3
    · refine ⟨2, by norm_num, ?_⟩
      simpa using h2
  · refine ⟨1, by norm_num, ?_⟩
    simpa using h1
