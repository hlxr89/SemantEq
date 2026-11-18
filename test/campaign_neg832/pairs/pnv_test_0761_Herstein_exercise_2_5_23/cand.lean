import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [CommGroup G] (H : Subgroup G) (hH : H.Normal) (a b : G) : ∃ (j : ℤ), a * b = b * a ^ j := sorry
