import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [Group G] [Fintype G] (hG : 2 < card G) : ∃ a : G, a = a⁻¹ ∧ a ≠ 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_1_18 {G : Type*} [Group G]
  [Fintype G] (hG2 : Even (card G)) :
  ∃ (a : G), a ≠ 1 ∧ a = a⁻¹ := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card 2 hG2.two_dvd
  refine ⟨a, ?_, (inv_eq_self_of_orderOf_eq_two ha).symm⟩
  intro ha1
  subst a
  simp at ha
