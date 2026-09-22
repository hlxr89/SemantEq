import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b c : ℤ) : ∃ n : ℕ, 0 < n ∧ ¬(∃ m : ℤ, m^2 = n^3 + a * n^2 + b * n + c) := by
  obtain ⟨n, hn, hnsqrt⟩ := exercise_1998_b6_assumed a b c
  have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
  refine ⟨n.toNat, by omega, ?_⟩
  rintro ⟨m, hm⟩
  apply hnsqrt
  refine ⟨|m|, ?_⟩
  rw [hcast] at hm
  have hmR : (m : ℝ)^2 = (n : ℝ)^3 + a*n^2 + b*n + c := by
    exact_mod_cast hm
  rw [← hmR, Real.sqrt_sq_eq_abs]
  exact_mod_cast rfl
