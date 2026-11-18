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
theorem problem_statement (c : ℝ) (h : ∀ n : ℕ, 0 < n → ∃ k : ℤ, (n : ℝ) ^ c = k) : 
  ∃ k : ℕ, c = ↑k := by
  have hc : ∀ n : ℤ, n > 0 → ∃ m : ℤ, (n : ℝ) ^ c = m := by
    intro n hn
    have hn_nonneg : 0 ≤ n := le_of_lt hn
    have hn_pos : 0 < n.toNat := by
      omega
    obtain ⟨m, hm⟩ := h n.toNat hn_pos
    refine ⟨m, ?_⟩
    have hn_eq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
    have hn_cast : (n.toNat : ℝ) = (n : ℝ) := by
      exact_mod_cast hn_eq
    simpa [hn_cast] using hm
  obtain ⟨m, hm_nonneg, hcm⟩ := putnam_1971_a6_assumed c hc
  refine ⟨m.toNat, ?_⟩
  calc
    c = (m : ℝ) := hcm
    _ = (m.toNat : ℝ) := by
      have hm_eq : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm_nonneg
      exact_mod_cast hm_eq.symm
