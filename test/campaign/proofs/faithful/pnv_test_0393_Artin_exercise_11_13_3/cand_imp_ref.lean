import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ∃ᶠ (p : ℕ) in atTop, Nat.Prime p ∧ p % 4 = 3 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_13_3 (N : ℕ):
  ∃ p ≥ N, Nat.Prime p ∧ p + 1 ≡ 0 [MOD 4] := by
  obtain ⟨p, hpN, hprime, hmod⟩ :=
    (Filter.frequently_atTop.mp dummy_assumed) N
  refine ⟨p, hpN, hprime, ?_⟩
  simp only [Nat.ModEq, Nat.zero_mod]
  omega
