import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (a b : G) (i : ℤ) (h : ∀ j ∈ ({i-1, i, i+1} : Finset ℤ), (a*b)^j = a^j * b^j) : Commute a b := sorry
