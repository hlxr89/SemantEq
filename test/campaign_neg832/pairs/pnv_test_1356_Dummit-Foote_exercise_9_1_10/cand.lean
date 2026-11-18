import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (I : Ideal R) [IsPrime I] (h : ∀ n : ℕ, ∃ I : Ideal R, IsPrime I ∧ I ≤ I ^ 2 ^ n) : ∃ n : ℕ, ∃ I : Ideal (R × R), IsPrime I ∧ I ≤ I ^ 2 ^ n := sorry
