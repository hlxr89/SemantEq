import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (a b : G) : ∃ c : G, c * (a * b) * c⁻¹ = b * a := sorry
