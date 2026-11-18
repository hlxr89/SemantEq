import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (hG : ∀ (H : Subgroup G), H ≠ ⊥ → H ≠ ⊤) : ∃ p : ℕ, Fact p.Prime ∧ Fintype.card G = p := sorry
