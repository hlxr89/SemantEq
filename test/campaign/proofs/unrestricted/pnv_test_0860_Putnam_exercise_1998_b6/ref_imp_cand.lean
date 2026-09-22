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
  obtain ⟨n, hn, hroot⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n, hn, ?_⟩
  rintro ⟨m, hm⟩
  apply hroot
  refine ⟨|m|, ?_⟩
  calc
    Real.sqrt ((n : ℝ)^3 + (a : ℝ)*(n : ℝ)^2 + (b : ℝ)*(n : ℝ) + (c : ℝ)) =
        Real.sqrt ((m : ℝ)^2) := by congr 1; exact_mod_cast hm
    _ = |(m : ℝ)| := Real.sqrt_sq_eq_abs (m : ℝ)
    _ = (|m| : ℤ) := by norm_cast
