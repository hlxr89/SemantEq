import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G % 2 = 0) (hG' : Fintype.card G > 2) : ∃ x : G, x ≠ 1 ∧ x ^ 2 = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_1_18 {G : Type*} [Group G]
  [Fintype G] (hG2 : Even (card G)) :
  ∃ (a : G), a ≠ 1 ∧ a = a⁻¹ := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card 2 (by simpa [even_iff_two_dvd] using hG2)
  have ha2 : a ^ 2 = 1 := by simpa [ha] using pow_orderOf_eq_one a
  refine ⟨a, ?_, ?_⟩
  · intro ha1
    subst a
    simp at ha
  · rw [eq_inv_iff_mul_eq_one]
    simpa [pow_two] using ha2
