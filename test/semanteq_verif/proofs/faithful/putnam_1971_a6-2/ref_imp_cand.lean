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
theorem problem_statement (c : ℝ) (h : ∀ n : ℕ, n > 0 → ∃ k : ℤ, (n : ℝ)^c = (k : ℝ)) : ∃ k : ℕ, c = (k : ℝ) := by
  obtain ⟨m, hm, hcm⟩ := putnam_1971_a6_assumed c (by
    intro n hn
    have hn0 : 0 < n.toNat := by omega
    obtain ⟨k, hk⟩ := h n.toNat hn0
    refine ⟨k, ?_⟩
    have hnt : (n.toNat : ℤ) = n := by omega
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast hnt
    rw [← hcast]
    exact hk)
  refine ⟨m.toNat, ?_⟩
  rw [hcm]
  have hmt : (m.toNat : ℤ) = m := by omega
  exact_mod_cast hmt.symm

