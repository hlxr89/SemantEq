import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy [Group G] [Finite G] (H : Subgroup G) [Subgroup.Normal H] (hH : H ≠ ⊤) : ∃ M : Subgroup G, H ≤ M ∧ ∀ N : Subgroup G, H ≤ N → N = M ∨ N = ⊤ := sorry
