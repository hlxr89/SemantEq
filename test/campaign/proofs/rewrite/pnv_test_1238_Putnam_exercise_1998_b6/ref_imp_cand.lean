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
  obtain ⟨n, hn, hnon⟩ := exercise_1998_b6_assumed a b c
  have hn0 : 0 ≤ n := le_of_lt hn
  refine ⟨n.toNat, ?_, ?_⟩
  · have hcast : (0 : ℤ) < (n.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hn0]
      exact hn
    exact_mod_cast hcast
  · intro hsquare
    obtain ⟨m, hm⟩ := hsquare
    apply hnon
    refine ⟨|m|, ?_⟩
    rw [Int.toNat_of_nonneg hn0] at hm
    have hmR := congrArg (fun z : ℤ => (z : ℝ)) hm
    push_cast at hmR
    rw [hmR, Real.sqrt_sq_eq_abs]
    norm_cast
