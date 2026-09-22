import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a b c : ℤ} : ∃ (n : ℕ) (hn : 0 < n), ¬ ∃ (m : ℤ), n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2 := by
  obtain ⟨n, hn, h⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.toNat, by omega, ?_⟩
  rintro ⟨m, hm⟩
  apply h
  refine ⟨|m|, ?_⟩
  rw [show (n.toNat : ℤ) = n by exact Int.toNat_of_nonneg hn.le] at hm
  have hmr : (n ^ 3 + a * n ^ 2 + b * n + c : ℝ) = (m : ℝ) ^ 2 := by
    exact_mod_cast hm
  rw [hmr, Real.sqrt_sq_eq_abs]
  exact_mod_cast rfl
