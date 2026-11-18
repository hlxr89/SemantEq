import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (h : Nat.card G = 2907) : ∃ H : Subgroup G, H.Normal ∧ H ≠ ⊥ := sorry
