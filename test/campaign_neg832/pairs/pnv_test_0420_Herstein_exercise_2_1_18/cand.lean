import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (h : Fintype.card G = 2 * Fintype.card G) : ∃ a : G, a ≠ 1 ∧ a = a⁻¹ := sorry
