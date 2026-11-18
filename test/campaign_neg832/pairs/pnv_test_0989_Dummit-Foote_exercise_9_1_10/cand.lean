import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (A : Type) [CommRing A] : ∃ s : Set (Ideal A), Set.Infinite s ∧ ∀ i ∈ s, ∃ a b : A, Prime (Ideal.span {a * b}) ∧ ∀ j ∈ s, j ≠ i → ¬ j ≤ Ideal.span {a * b} := sorry
