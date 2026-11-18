import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (h : Fintype.card G = 2^4 * 7) : ∃ H : Subgroup G, H ≠ ⊥ ∧ H ≠ ⊤ := sorry
