import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (G : Type*) [Group G] [Fintype G] (σ : G →* G) (hs : ∀ g : G, σ g = g ↔ g = 1) : (∀ g : G, σ (σ g) = g) → ∀ (a b : G), a * b = b * a := sorry
