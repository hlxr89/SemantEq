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
  obtain ⟨k, hk_nonneg, hc⟩ := putnam_1971_a6_assumed c (by
    intro n hn
    have hn_nonneg : 0 ≤ n := le_of_lt hn
    obtain ⟨m, hm⟩ := h n.toNat (by omega)
    refine ⟨m, ?_⟩
    have hn_eq : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hn_nonneg
    rw [hn_eq] at hm
    exact hm)
  refine ⟨k, hc, ?_⟩
  rw [hc]
  exact_mod_cast hk_nonneg
