import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (hG : ∀ (A : Subgroup G), A.Normal) (a b : G) : ∃ (j : ℤ), b * a = a ^ j * b := sorry
