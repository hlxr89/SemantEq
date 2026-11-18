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
  obtain ⟨m, hm, hcm⟩ := putnam_1971_a6_assumed c (by
    intro n hn
    have hn0 : 0 < n.toNat := by omega
    obtain ⟨k, hk⟩ := h n.toNat hn0
    refine ⟨k, ?_⟩
    have hn_eq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
    have hn_real : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hn_eq
    simpa [hn_real] using hk)
  refine ⟨m.toNat, ?_⟩
  have hm_eq : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
  calc
    c = (m : ℝ) := hcm
    _ = (m.toNat : ℝ) := by exact_mod_cast hm_eq.symm
