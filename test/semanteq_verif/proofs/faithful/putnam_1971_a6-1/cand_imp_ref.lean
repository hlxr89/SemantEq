import Mathlib

open Set MvPolynomial

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (c : ℝ) (h : ∀ n : ℕ, 0 < n → ∃ k : ℤ, (n : ℝ) ^ c = k) : 
  ∃ k : ℕ, c = ↑k := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1971_a6
(c : ℝ)
(hc : ∀ n : ℤ, n > 0 → ∃ m : ℤ, (n : ℝ)^c = m)
: ∃ m : ℤ, m ≥ 0 ∧ c = m := by
  obtain ⟨k, hck⟩ := problem_statement_assumed c (by
    intro n hn
    obtain ⟨m, hm⟩ := hc (n : ℤ) (by exact_mod_cast hn)
    exact ⟨m, by simpa using hm⟩)
  refine ⟨(k : ℤ), by positivity, ?_⟩
  simpa using hck
