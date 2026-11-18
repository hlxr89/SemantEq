import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {H : Subgroup G} (hH : H ≠ ⊤) : ∃ (M : Subgroup G), M ≠ ⊤ ∧ ∀ (M' : Subgroup G), M' ≠ ⊤ → M' ≠ M → M' ≤ H → M' = H ∨ M' = ⊤ := sorry
