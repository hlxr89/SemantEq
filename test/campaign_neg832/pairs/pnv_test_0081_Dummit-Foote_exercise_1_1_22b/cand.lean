import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {a b : G} (hab : Commute a b) (hb : b ∈ (center G : Subgroup G)) : Commute b a := sorry
