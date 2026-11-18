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
  obtain ⟨m, hm, hcm⟩ := putnam_1971_a6_assumed c (fun n hn => by
    have hn_nonneg : 0 ≤ n := le_of_lt hn
    have hn_toNat_pos : 0 < n.toNat := Int.natCast_pos.mp (by
      rw [Int.toNat_of_nonneg hn_nonneg]
      exact hn)
    obtain ⟨k, hk⟩ := h n.toNat hn_toNat_pos
    refine ⟨k, ?_⟩
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn_nonneg] at hk
    exact hk)
  refine ⟨m.toNat, ?_⟩
  rw [hcm, ← Int.cast_natCast, Int.toNat_of_nonneg hm]
