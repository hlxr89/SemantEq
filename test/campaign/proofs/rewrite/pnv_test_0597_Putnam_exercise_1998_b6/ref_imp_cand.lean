import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a b c : ℤ} : ∃ n : ℕ, ¬ ∃ m : ℤ, m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
  obtain ⟨n, hn, hnonint⟩ := exercise_1998_b6_assumed a b c
  have hn0 : 0 ≤ n := le_of_lt hn
  have hnat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  refine ⟨n.toNat, ?_⟩
  rintro ⟨m, hm⟩
  apply hnonint
  refine ⟨|m|, ?_⟩
  rw [← hnat]
  have hm_real : (m : ℝ) ^ 2 =
      ((n.toNat : ℤ) : ℝ) ^ 3 + (a : ℝ) * ((n.toNat : ℤ) : ℝ) ^ 2 +
        (b : ℝ) * (n.toNat : ℤ) + c := by
    exact_mod_cast hm
  rw [← hm_real]
  simpa only [Int.cast_pow, Int.cast_abs] using Real.sqrt_sq_eq_abs (m : ℝ)
