import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy (G : Type u) [Group G] [Fintype G] (h : Fintype.card G = 2^2^2^2) : ¬IsSimpleGroup G := sorry
