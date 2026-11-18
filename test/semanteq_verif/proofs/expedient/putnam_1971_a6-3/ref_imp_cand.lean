import Mathlib

open Set MvPolynomial

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1971_a6_assumed
(c : ℝ)
(hc : ∀ n : ℤ, n > 0 → ∃ m : ℤ, (n : ℝ)^c = m)
: ∃ m : ℤ, m ≥ 0 ∧ c = m :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (c : ℝ) (h : ∀ n : ℕ, n > 0 → ∃ k : ℤ, (n : ℝ)^c = k) : ∃ k : ℤ, c = k ∧ c ≥ 0 := by
  obtain ⟨m, hm, hcm⟩ := putnam_1971_a6_assumed c fun n hn => by
    obtain ⟨k, hk⟩ := h n.toNat (by omega)
    have heq : (n.toNat : ℝ) = (n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (le_of_lt hn)
    exact ⟨k, by simpa [heq] using hk⟩
  refine ⟨m, hcm, ?_⟩
  rw [hcm]
  exact_mod_cast hm
