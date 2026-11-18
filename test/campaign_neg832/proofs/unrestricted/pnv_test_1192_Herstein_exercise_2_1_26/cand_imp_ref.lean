import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Finite G] (a : G) : ∃ n : ℕ, a ^ n = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), n > 0 ∧ a ^ n = 1 := by
  have _ := dummy_assumed a
  have hp : (Submonoid.powers a : Set G).Finite := Set.toFinite _
  exact (finite_powers.mp hp).exists_pow_eq_one
