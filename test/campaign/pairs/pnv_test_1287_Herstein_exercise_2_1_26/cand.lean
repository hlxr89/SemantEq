import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (a : G) : ∃ n > 0, a ^ n = 1 := sorry
