import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (σ : G →* G) (hσ : ∀ g : G, σ (σ g) = g) (hσ_fix : ∀ g : G, σ g = g ↔ g = 1) : ∀ a b : G, a * b = b * a := sorry
