import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (hG : Even (Fintype.card G)) : ∃ a : G, a ≠ 1 ∧ a = a⁻¹ := sorry
