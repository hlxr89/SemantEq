import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (R : Type*) [CommRing R] : ∃ (P : ℕ → Ideal (Polynomial R)), (∀ n : ℕ, Ideal.IsPrime (P n)) ∧ (∀ m n : ℕ, m ≠ n → P m ≠ P n) := sorry
