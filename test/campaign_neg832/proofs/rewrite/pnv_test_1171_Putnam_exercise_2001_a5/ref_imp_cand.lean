import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2001_a5_assumed :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a : ℕ} (ha : 0 < a) : ∃! (n : ℕ), a ^ (n + 1) - (a + 1) ^ n = 2001 := by
  -- not proved: the reference gives one unique pair, not a solution for every positive a
  sorry
