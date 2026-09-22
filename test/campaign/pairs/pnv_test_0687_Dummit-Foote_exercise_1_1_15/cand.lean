import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (l : List G) : (l.prod)⁻¹ = (l.map Inv.inv).reverse.prod := sorry
