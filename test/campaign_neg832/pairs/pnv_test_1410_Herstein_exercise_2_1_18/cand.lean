import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Finite G] (h : ∀ a : G, a ≠ 1 → a * a = 1) : ∃ a : G, a ≠ 1 ∧ a * a = 1 := sorry
