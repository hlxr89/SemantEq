import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (hG : ∀ H : Subgroup G, H.Normal) (a b : G) : ∃ j : ℤ, b * a = a ^ j * b := sorry
