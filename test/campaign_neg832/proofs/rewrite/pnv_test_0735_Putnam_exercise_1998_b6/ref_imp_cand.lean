import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a b c : ℤ} : ∃ n : ℕ, ¬∃ m : ℕ, m^2 = n^3 + a * n^2 + b * n + c := by
  obtain ⟨n, hn, hnsqrt⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.natAbs, ?_⟩
  rintro ⟨m, hm⟩
  apply hnsqrt
  refine ⟨m, ?_⟩
  have hn0 : 0 ≤ n := le_of_lt hn
  have hncast : (n.natAbs : ℤ) = n := by
    rw [Int.natCast_natAbs, abs_of_nonneg hn0]
  have hm' : (m : ℤ)^2 = n^3 + a*n^2 + b*n + c := by
    simpa only [hncast] using hm
  have hmR : ((m : ℤ) : ℝ)^2 =
      (n^3 + a*n^2 + b*n + c : ℤ) := by
    exact_mod_cast hm'
  push_cast at hmR
  rw [← hmR]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  norm_cast
