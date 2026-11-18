import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [hp : Fact (∀ H : Subgroup G, H = ⊥ ∨ H = ⊤)] : ∃ (g : G), IsCyclic (Subgroup.closure ({g} : Set G)) := sorry
