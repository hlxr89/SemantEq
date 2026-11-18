import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {p : ℕ} (hp : Fact p.Prime) (hsub : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤) : IsCyclic G := sorry
