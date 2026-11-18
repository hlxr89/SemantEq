import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (hR : IsDomain R) (hgcd : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ d, ∃ r s : R, d = r * a + s * b ∧ ∀ t : R, t ∣ a → t ∣ b → t ∣ d) (hnoetherian : ∀ a : ℕ → R, (∀ n : ℕ, a (n + 1) ∣ a n) → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → IsUnit (a n)): IsPrincipalIdealRing R := sorry
