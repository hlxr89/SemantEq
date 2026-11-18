import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hG : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤) : IsCyclic G := sorry
