import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_3_2 {G : Type*} [Group G] (a b : G) :
  ∃ g : G, b* a = g * a * b * g⁻¹ := sorry
