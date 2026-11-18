import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_1_18_assumed {G : Type*} [Group G]
  [Fintype G] (hG2 : Even (card G)) :
  ∃ (a : G), a ≠ 1 ∧ a = a⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy [Group G] [Fintype G] (hG : 2 < card G) : ∃ a : G, a = a⁻¹ ∧ a ≠ 1 := by
  -- not proved: false for the cyclic group of order three
  sorry
