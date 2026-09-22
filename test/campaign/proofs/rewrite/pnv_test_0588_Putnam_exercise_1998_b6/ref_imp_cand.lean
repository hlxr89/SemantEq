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
  obtain ⟨n, hn, hnonint⟩ := exercise_1998_b6_assumed a b c
  refine ⟨n.toNat, ?_, ?_⟩
  · have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
    have hn' : (0 : ℤ) < (n.toNat : ℤ) := hncast.symm ▸ hn
    exact_mod_cast hn'
  · rintro ⟨k, hk⟩
    apply hnonint
    refine ⟨|k|, ?_⟩
    have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
    have hk' : (k : ℝ)^2 = n^3 + a*n^2 + b*n + c := by
      rw [← hncast]
      exact_mod_cast hk
    rw [Int.cast_abs, ← Real.sqrt_sq_eq_abs k, hk']
