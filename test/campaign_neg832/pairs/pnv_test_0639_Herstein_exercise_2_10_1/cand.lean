import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (G : Type*) [Group G] (N : Subgroup G) [hN : N.Normal] (b : G) {p : ℕ} (hb : orderOf b = p) (hNb : ¬b ∈ N) : N ⊓ Subgroup.center G = ⊥ := sorry
