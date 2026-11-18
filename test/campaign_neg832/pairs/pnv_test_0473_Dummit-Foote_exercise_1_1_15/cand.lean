import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (G : Type*) [Group G] [DecidableEq G] (a₁ a₂ : G) : (a₁ * a₂)⁻¹ = a₂⁻¹ * a₁⁻¹ := sorry
