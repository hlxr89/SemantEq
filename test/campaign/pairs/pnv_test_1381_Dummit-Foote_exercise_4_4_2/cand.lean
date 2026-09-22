import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [CommGroup G] [Fintype G] (h : Fintype.card G = p * q) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : p ≠ q) : IsCyclic G := sorry
