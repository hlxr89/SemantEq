import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b c : ℤ) : ∃ (n : ℤ) (H : n > 0), ¬(∃ (m : ℤ), n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2) := by
  obtain ⟨n, hn, h⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  apply h
  refine ⟨|m|, ?_⟩
  have hm' : (n : ℝ) ^ 3 + a * n ^ 2 + b * n + c = (m : ℝ) ^ 2 := by
    exact_mod_cast hm
  rw [hm']
  simpa using Real.sqrt_sq_eq_abs (m : ℝ)
