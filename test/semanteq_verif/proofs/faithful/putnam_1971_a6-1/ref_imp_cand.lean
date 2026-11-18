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
    have hnt : 0 < n.toNat := by omega
    obtain ⟨k, hk⟩ := h n.toNat hnt
    refine ⟨k, ?_⟩
    have hn_nonneg : 0 ≤ n := le_of_lt hn
    have hn_cast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
    have hn_real : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hn_cast
    rw [hn_real] at hk
    exact hk)
  refine ⟨m.toNat, ?_⟩
  have hm_cast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
  have hm_real : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast hm_cast
  rw [hm_real]
  exact hcm
