import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (G : Type*) [Group G] (h : ∀ (a b : G) (i : ℕ), (a * b)^i = a^i * b^i → (a * b)^(i+1) = a^(i+1) * b^(i+1)) : ∀ a b : G, a * b = b * a := sorry
