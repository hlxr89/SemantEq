import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1998_b6_assumed (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b c : ℤ) (h : ∃ n : ℕ, √(n^3+a*n^2+b*n+c) ≠ n) : ∃ n : ℕ, 0 < n ∧ √(n^3+a*n^2+b*n+c) ≠ n := by
  obtain ⟨n, hn, hs⟩ := exercise_1998_b6_assumed a b c
  have hn0 : 0 ≤ n := le_of_lt hn
  have hcast : (n.toNat : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn0
  refine ⟨n.toNat, by omega, ?_⟩
  intro heq
  apply hs
  refine ⟨n, ?_⟩
  simpa [hcast] using heq
