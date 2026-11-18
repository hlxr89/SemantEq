import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a n : ℕ) (ha : a ≠ 0) : a ^ (n + 1) - (a + 1) ^ n = 2001 → (a, n) = (9, 2) ∨ (a, n) = (10, 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  -- not proved: the candidate is inconsistent at (13, 2), so this direction requires forbidden explosion rather than transport
  sorry
