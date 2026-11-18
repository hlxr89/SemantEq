import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (G : Type*) [Group G] [Fintype G]: Fintype.card G = 1 ∨ ∃ p : ℕ, Nat.Prime p ∧ Fintype.card G = p ∨ Fintype.card G = p^2 := sorry
