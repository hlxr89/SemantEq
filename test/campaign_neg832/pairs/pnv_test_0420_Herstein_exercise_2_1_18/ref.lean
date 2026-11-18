import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem exercise_2_1_18 {G : Type*} [Group G]
  [Fintype G] (hG2 : Even (card G)) :
  ∃ (a : G), a ≠ 1 ∧ a = a⁻¹ := sorry
