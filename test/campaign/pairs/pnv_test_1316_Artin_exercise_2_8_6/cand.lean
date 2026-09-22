import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {G H : Type*} [Group G] [Group H] : center (G × H) = (center G × center H) := sorry
