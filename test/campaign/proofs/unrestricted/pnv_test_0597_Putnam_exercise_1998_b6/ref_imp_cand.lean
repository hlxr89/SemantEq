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
  obtain ⟨n, hn, hnsqrt⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.toNat, ?_⟩
  rintro ⟨m, hm⟩
  have hncast : (n.toNat : ℤ) = n := by omega
  apply hnsqrt
  refine ⟨|m|, ?_⟩
  have hm_real : ((m : ℝ) ^ 2) =
      (n : ℝ) ^ 3 + (a : ℝ) * (n : ℝ) ^ 2 + (b : ℝ) * n + c := by
    exact_mod_cast (hm.trans (by rw [hncast]))
  rw [← hm_real]
  simpa using (Real.sqrt_sq_eq_abs (m : ℝ))
