import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G = 6545) : ¬ IsSimpleGroup G := sorry
