import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} (φ : G →* G) : ∀ (g : G), g ∈ P → φ g ∈ P := sorry
