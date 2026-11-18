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
  obtain ⟨m, hm, hcm⟩ := putnam_1971_a6_assumed c (by
    intro n hn
    have hn0 : 0 ≤ n := le_of_lt hn
    have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    have hnNat : n.toNat > 0 := Int.natCast_pos.mp (by
      rw [hcast]
      exact hn)
    obtain ⟨k, hk⟩ := h n.toNat hnNat
    refine ⟨k, ?_⟩
    rw [← hcast, Int.cast_natCast]
    exact hk)
  refine ⟨m, hcm, ?_⟩
  rw [hcm]
  exact Int.cast_nonneg_iff.mpr hm
