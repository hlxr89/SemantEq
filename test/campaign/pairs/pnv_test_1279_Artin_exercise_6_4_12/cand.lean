import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (hG : Fintype G) (hG_order : Fintype.card G = 224) : ¬ IsSimpleGroup G := sorry
