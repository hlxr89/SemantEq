import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (G : Type u) [Group G] [Finite G] (H : Subgroup G) (hH : H ≠ ⊤) : ∃ M : Subgroup G, M ≤ H ∧ (∀ (L : Subgroup G), H ≤ L → M = ⊤ ∨ M = L) := sorry
