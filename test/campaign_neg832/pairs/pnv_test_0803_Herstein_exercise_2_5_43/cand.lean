import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (hcard : Fintype.card G = 9) : ∀ g : G, g ^ 2 = 1 ∨ g ^ 6 = 1 := sorry
