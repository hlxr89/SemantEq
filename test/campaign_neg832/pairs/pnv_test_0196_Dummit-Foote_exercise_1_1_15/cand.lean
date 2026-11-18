import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (a1 a2 a3 : G) : (a1 * a2 * a3)⁻¹ = a3⁻¹ * a2⁻¹ * a1⁻¹ := sorry
