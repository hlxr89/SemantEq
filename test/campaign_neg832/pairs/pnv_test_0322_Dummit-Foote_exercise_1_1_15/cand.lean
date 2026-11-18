import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (a b c : G) (h : a * b = c) : a⁻¹ * b⁻¹ = c⁻¹ := sorry
