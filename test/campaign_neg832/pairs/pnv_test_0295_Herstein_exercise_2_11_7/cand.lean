import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (G : Type*) [Group G] {P : Subgroup G} (hP : IsPGroup p P) (hPn : P.Normal) (hPs : IsPGroup p (G ⧸ P)) : ∀ (φ : G →* G), φ.range = P := sorry
