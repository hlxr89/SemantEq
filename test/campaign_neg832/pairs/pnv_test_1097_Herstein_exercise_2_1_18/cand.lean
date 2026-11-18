import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy [Group G] [Fintype G] (hG : 2 < card G) : ∃ a : G, a = a⁻¹ ∧ a ≠ 1 := sorry
