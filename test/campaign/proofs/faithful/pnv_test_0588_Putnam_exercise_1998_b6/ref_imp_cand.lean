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
  refine ⟨n.toNat, by omega, ?_⟩
  rintro ⟨k, hk⟩
  apply hnsqrt
  refine ⟨|k|, ?_⟩
  rw [show (n.toNat : ℤ) = n by omega] at hk
  have hsqrt : Real.sqrt (n^3 + a*n^2 + b*n + c) = |(k : ℝ)| := by
    calc
      Real.sqrt (n^3 + a*n^2 + b*n + c) = Real.sqrt ((k : ℝ)^2) := by
        congr 1
        exact_mod_cast hk.symm
      _ = |(k : ℝ)| := Real.sqrt_sq_eq_abs _
  exact hsqrt.trans (@Int.cast_abs ℝ _ _ _ k).symm
