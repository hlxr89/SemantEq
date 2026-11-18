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
  rcases exercise_1998_b6_assumed a (b - 1) c with ⟨n, hn, hnonint⟩
  refine ⟨n, hn, ?_⟩
  intro heq
  apply hnonint
  refine ⟨0, ?_⟩
  have heqZ : n^3 + a * n^2 + b * n + c = n := by
    exact_mod_cast heq
  have hzero : n^3 + a * n^2 + (b - 1) * n + c = 0 := by
    linarith
  have hzeroR : (n : ℝ)^3 + a * n^2 + ((b - 1 : ℤ) : ℝ) * n + c = 0 := by
    exact_mod_cast hzero
  rw [hzeroR]
  norm_num
