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
    obtain ⟨k, hk⟩ := h n.toNat (by omega)
    have hn_eq : (n.toNat : ℤ) = n := by omega
    have hn_real : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hn_eq
    refine ⟨k, ?_⟩
    rw [← hn_real]
    exact hk)
  refine ⟨m.toNat, hcm.trans ?_⟩
  exact_mod_cast (Int.toNat_of_nonneg hm).symm
