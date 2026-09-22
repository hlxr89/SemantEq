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
  rcases exercise_1998_b6_assumed a b c with ⟨n, hn, hnroot⟩
  refine ⟨n.toNat, ?_, ?_⟩
  · omega
  · rintro ⟨m, hm⟩
    apply hnroot
    refine ⟨|m|, ?_⟩
    rw [Int.toNat_of_nonneg (le_of_lt hn)] at hm
    norm_cast at hm ⊢
    rw [← hm]
    simpa using (Real.sqrt_sq_eq_abs (m : ℝ))
