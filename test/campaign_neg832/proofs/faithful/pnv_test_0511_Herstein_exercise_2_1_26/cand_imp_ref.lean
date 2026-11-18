import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] [DecidableEq G] {p z : ℕ} (hp : Nat.Prime p) (hz : Fintype.card G = p ^ z) (n : ℕ) [hzp : Fact (z ≤ p)] : ∃ m : ℕ, 0 < m ∧ a ^ m = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), n > 0 ∧ a ^ n = 1 := by
  -- not proved: the antecedent concerns a natural-number a and only prime-power-cardinality groups
  sorry
