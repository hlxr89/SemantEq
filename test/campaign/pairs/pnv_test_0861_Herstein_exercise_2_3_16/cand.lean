import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (h : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤) : ∃ p : ℕ, Nat.Prime p ∧ ∃ g : G, orderOf g = p ∧ (∀ h : G, h ∈ Subgroup.zpowers g) := sorry
