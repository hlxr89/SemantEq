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
  obtain ⟨n, hn, hroot⟩ := exercise_1998_b6_assumed a b c
  have hn0 : 0 ≤ n := le_of_lt hn
  refine ⟨n.toNat, ?_, ?_⟩
  · omega
  · rintro ⟨k, hk⟩
    apply hroot
    refine ⟨|k|, ?_⟩
    have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    have hk' : k ^ 2 = n ^ 3 + a * n ^ 2 + b * n + c := by
      simpa [hcast] using hk
    have hkR :
        (n : ℝ) ^ 3 + (a : ℝ) * (n : ℝ) ^ 2 + (b : ℝ) * n + c = (k : ℝ) ^ 2 := by
      exact_mod_cast hk'.symm
    rw [hkR, Real.sqrt_sq_eq_abs]
    norm_num
