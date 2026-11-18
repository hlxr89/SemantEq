import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] (h : Fintype.card G = 2 * Fintype.card G) : ∃ a : G, a ≠ 1 ∧ a = a⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_1_18 {G : Type*} [Group G]
  [Fintype G] (hG2 : Even (card G)) :
  ∃ (a : G), a ≠ 1 ∧ a = a⁻¹ := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := G) 2 hG2.two_dvd
  have ha' : a ^ 2 = 1 ∧ a ≠ 1 := orderOf_eq_prime_iff.mp ha
  refine ⟨a, ha'.2, ?_⟩
  exact eq_inv_iff_mul_eq_one.mpr (by simpa [pow_two] using ha'.1)
