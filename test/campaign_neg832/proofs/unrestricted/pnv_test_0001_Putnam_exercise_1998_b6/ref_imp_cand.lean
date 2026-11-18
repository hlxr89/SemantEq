import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b c : ℤ) : ∃ (n : ℕ) (H : 0 < n), √(n^3 + a*n^2 + b*n + c) ≠ n := by
  obtain ⟨n, hn, hnonint⟩ := exercise_1998_b6_assumed a b c
  have hn0 : 0 ≤ n := le_of_lt hn
  refine ⟨n.toNat, ?_, ?_⟩
  · omega
  · intro heq
    apply hnonint
    refine ⟨n, ?_⟩
    have hcast : (n.toNat : ℝ) = n := by
      exact_mod_cast Int.toNat_of_nonneg hn0
    simpa only [hcast] using heq
