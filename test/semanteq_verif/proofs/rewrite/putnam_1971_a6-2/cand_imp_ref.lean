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
  obtain ⟨k, hck⟩ := problem_statement_assumed c (fun n hn => by
    obtain ⟨m, hm⟩ := hc (n : ℤ) (Int.natCast_pos.mpr hn)
    refine ⟨m, ?_⟩
    rw [Int.cast_natCast] at hm
    exact hm)
  refine ⟨(k : ℤ), Int.natCast_nonneg k, ?_⟩
  rw [Int.cast_natCast]
  exact hck
