import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {H : Subgroup G} (hH : H ≠ ⊤) : ∃ M : Subgroup G, M ≠ ⊤ ∧ H ≤ M ∧ ∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤ := sorry
