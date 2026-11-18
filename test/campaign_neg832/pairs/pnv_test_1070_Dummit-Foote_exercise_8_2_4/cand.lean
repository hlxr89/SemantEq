import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (R : Type*) [CommRing R] [IsDomain R] (h1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ d r s : R, d ∣ a ∧ d ∣ b ∧ d = r * a + s * b) (h2 : ∀ (a : ℕ → R), (∀ i, a (i + 1) ∣ a i) → ∃ N, ∀ n ≥ N, IsUnit (a n) ↔ IsUnit (a N)) : IsPrincipalIdealRing R := sorry
