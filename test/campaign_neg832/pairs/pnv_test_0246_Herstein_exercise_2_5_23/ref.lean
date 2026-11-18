import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem exercise_2_5_23 {G : Type*} [Group G]
  (hG : ∀ (H : Subgroup G), H.Normal) (a b : G) :
  ∃ (j : ℤ) , b*a = a^j * b:= sorry
