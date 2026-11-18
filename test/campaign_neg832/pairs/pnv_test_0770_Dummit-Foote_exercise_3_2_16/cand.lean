import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (p : ℕ) (hp : p.Prime) {G : Type*} [CommGroup G] [Fintype G] (hG : IsCyclic G) : ∀ (a : G), a ^ p = a := sorry
