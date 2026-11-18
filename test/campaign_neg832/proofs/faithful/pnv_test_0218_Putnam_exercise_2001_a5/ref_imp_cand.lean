import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_2001_a5_assumed :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a n : ℕ) (ha : 0 < a) (hn : 0 < n) (h_eq : a^(n+1) - (a+1)^n = 2001) : (a, n) = (10, 3) := by
  -- not proved: the statements are not equivalent; (13, 2) satisfies the predicate, while (10, 3) does not
  sorry
