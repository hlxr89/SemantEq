import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (a b c d : G) (hb : a * b = c) (hd : c * d = 1) : d * b = a := sorry
