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
  refine ⟨n.toNat, ?_, ?_⟩
  · omega
  · rintro ⟨m, hm⟩
    apply hnsqrt
    refine ⟨|m|, ?_⟩
    have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
    rw [← hn']
    have hmR := congrArg (fun z : ℤ => (z : ℝ)) hm
    push_cast at hmR
    push_cast
    rw [← hmR, Real.sqrt_sq_eq_abs]
