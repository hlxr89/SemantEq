import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a n : ℕ) (ha : 0 < a) (hn : 0 < n) (h_eq : a^(n+1) - (a+1)^n = 2001) : (a, n) = (10, 3) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  have h_fixed : (13 : ℕ) > 0 ∧ (2 : ℕ) > 0 ∧
      (13 : ℕ) ^ ((2 : ℕ) + 1) - ((13 : ℕ) + 1) ^ (2 : ℕ) = 2001 := by
    norm_num
  refine ⟨(13, 2), h_fixed, ?_⟩
  intro p hp
  have hp_fixed := dummy_assumed p.1 p.2 hp.1 hp.2.1 hp.2.2
  have h_witness_fixed := dummy_assumed 13 2 h_fixed.1 h_fixed.2.1 h_fixed.2.2
  exact hp_fixed.trans h_witness_fixed.symm
