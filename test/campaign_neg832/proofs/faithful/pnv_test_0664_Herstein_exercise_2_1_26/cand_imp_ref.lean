import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Finite G] (a : G) : ∃ (n : ℕ), a ^ n = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), n > 0 ∧ a ^ n = 1 := by
  obtain ⟨n, hn⟩ := dummy_assumed a
  refine ⟨n + orderOf a, Nat.add_pos_right n (orderOf_pos a), ?_⟩
  rw [pow_add, hn, pow_orderOf_eq_one, one_mul]
