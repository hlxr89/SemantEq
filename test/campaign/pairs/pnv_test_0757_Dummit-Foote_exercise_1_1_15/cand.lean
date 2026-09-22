import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {n : ℕ} (l : List G) (hl : l.length = n) : l.prod⁻¹ = (l.map (Equiv.inv G).toFun).reverse.prod := sorry
