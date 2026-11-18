import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {a b : G} : a * b = b * a ↔ ∃ c : G, c * a * c⁻¹ = b := sorry
