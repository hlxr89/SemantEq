import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] : Fintype.card G = 9 → ∃ (g h : G), g ≠ h ∧ g * h = h * g := sorry
