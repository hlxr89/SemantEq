import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : H ≠ ⊤) : ∃ (M : Subgroup G), H ≤ M ∧ M ≠ ⊤ ∧ ∀ (K : Subgroup G), H ≤ K → K = M ∨ K = ⊤ := sorry
