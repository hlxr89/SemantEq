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
  obtain ⟨n, hn, hnon⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.toNat, ?_⟩
  rintro ⟨m, hm⟩
  apply hnon
  refine ⟨|m|, ?_⟩
  have hnt : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
  rw [← hnt]
  have hmR : (m : ℝ) ^ 2 =
      ((n.toNat : ℤ) : ℝ) ^ 3 + (a : ℝ) * ((n.toNat : ℤ) : ℝ) ^ 2 +
        (b : ℝ) * ((n.toNat : ℤ) : ℝ) + (c : ℝ) := by
    exact_mod_cast hm
  rw [← hmR]
  simpa using Real.sqrt_sq_eq_abs (m : ℝ)
