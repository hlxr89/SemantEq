import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {G H : Type*} [Group G] [Group H] : (center (G × H) : Set (G × H)) = (center G : Set G) ×ˢ (center H : Set H) := sorry
