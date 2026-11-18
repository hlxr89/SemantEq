import Mathlib

open Set MvPolynomial

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (c : ℝ) (h : ∀ n : ℕ, n > 0 → ∃ k : ℤ, (n : ℝ)^c = k) : ∃ k : ℤ, c = k ∧ c ≥ 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1971_a6
(c : ℝ)
(hc : ∀ n : ℤ, n > 0 → ∃ m : ℤ, (n : ℝ)^c = m)
: ∃ m : ℤ, m ≥ 0 ∧ c = m := by
  obtain ⟨k, hc, hc_nonneg⟩ := problem_statement_assumed c (by
    intro n hn
    simpa using hc (n : ℤ) (by omega))
  refine ⟨k, ?_, hc⟩
  rw [hc] at hc_nonneg
  exact_mod_cast hc_nonneg
