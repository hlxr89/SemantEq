import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (h : ∀ (H : Subgroup G), H.Normal) (a b : G) : ∃ j : ℤ, a ^ j * b = b * a := sorry
