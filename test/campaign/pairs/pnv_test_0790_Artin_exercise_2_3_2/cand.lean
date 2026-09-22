import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy (G : Type*) [Group G] (a b : G) : ∃ g : G, g * (a * b) * g⁻¹ = b * a := sorry
