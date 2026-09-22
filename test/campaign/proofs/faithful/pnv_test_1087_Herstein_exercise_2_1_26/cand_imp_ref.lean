import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] (a : G) : ∃ n : ℕ, 0 < n ∧ a ^ n = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), n > 0 ∧ a ^ n = 1 := by
  exact dummy_assumed a
