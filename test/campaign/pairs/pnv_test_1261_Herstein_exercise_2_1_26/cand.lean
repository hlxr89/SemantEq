import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy [Group G] [Finite G] (a : G) : ∃ n : ℕ, n > 0 ∧ a ^ n = 1 := sorry
