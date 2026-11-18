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
  have hc : ∀ n : ℤ, n > 0 → ∃ m : ℤ, (n : ℝ)^c = m := by
    intro n hn
    have hn' := hn
    rw [← Int.toNat_of_nonneg (le_of_lt hn)] at hn'
    have hnat : 0 < n.toNat := by
      exact_mod_cast hn'
    obtain ⟨k, hk⟩ := h n.toNat hnat
    refine ⟨k, ?_⟩
    rw [← Int.toNat_of_nonneg (le_of_lt hn)]
    exact hk
  obtain ⟨m, hm, hcm⟩ := putnam_1971_a6_assumed c hc
  refine ⟨m.toNat, ?_⟩
  rw [hcm]
  exact congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hm) |>.symm
