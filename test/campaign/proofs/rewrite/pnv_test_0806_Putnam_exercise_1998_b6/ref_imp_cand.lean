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
  obtain ⟨n, hn, hnsqrt⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.toNat, ?_⟩
  intro hsquare
  obtain ⟨m, hm⟩ := hsquare
  apply hnsqrt
  refine ⟨|m|, ?_⟩
  have hn_coe : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
  have hm' : m ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
    simpa only [hn_coe] using hm
  have habs : ((|m| : ℤ) : ℝ) = |(m : ℝ)| := by
    exact_mod_cast rfl
  rw [habs, ← Real.sqrt_sq_eq_abs (m : ℝ)]
  congr 1
  exact_mod_cast hm'.symm
