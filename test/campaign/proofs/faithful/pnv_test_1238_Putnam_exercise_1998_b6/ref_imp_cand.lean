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
  rcases exercise_1998_b6_assumed a b c with ⟨n, hn, hns⟩
  have hn0 : 0 ≤ n := le_of_lt hn
  have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  refine ⟨n.toNat, ?_, ?_⟩
  · omega
  · rintro ⟨m, hm⟩
    apply hns
    refine ⟨|m|, ?_⟩
    have hmZ : n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2 := by
      simpa [hcast] using hm
    have hm' : (n ^ 3 + a * n ^ 2 + b * n + c : ℝ) = (m : ℝ) ^ 2 := by
      exact_mod_cast hmZ
    rw [hm']
    simpa using (Real.sqrt_sq_eq_abs (m : ℝ))
