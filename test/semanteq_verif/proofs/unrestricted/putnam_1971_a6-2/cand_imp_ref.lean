import Mathlib

open Set MvPolynomial

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (c : ℝ) (h : ∀ n : ℕ, n > 0 → ∃ k : ℤ, (n : ℝ)^c = (k : ℝ)) : ∃ k : ℕ, c = (k : ℝ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1971_a6
(c : ℝ)
(hc : ∀ n : ℤ, n > 0 → ∃ m : ℤ, (n : ℝ)^c = m)
: ∃ m : ℤ, m ≥ 0 ∧ c = m :=
by
  obtain ⟨k, hk⟩ := problem_statement_assumed c (by
    intro n hn
    obtain ⟨m, hm⟩ := hc (n : ℤ) (by exact_mod_cast hn)
    exact ⟨m, by simpa using hm⟩)
  exact ⟨(k : ℤ), by positivity, by exact_mod_cast hk⟩
