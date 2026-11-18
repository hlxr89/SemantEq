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
  obtain ⟨k, hk, hck⟩ := putnam_1971_a6_assumed c (by
    intro n hn
    have hnpos : n.toNat > 0 := by omega
    obtain ⟨k, hk⟩ := h n.toNat hnpos
    refine ⟨k, ?_⟩
    have hn_eq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
    have hcast : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hn_eq
    simpa [hcast] using hk)
  refine ⟨k, hck, ?_⟩
  rw [hck]
  exact_mod_cast hk
