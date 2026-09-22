import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy : ∃ S : Set ℕ, (∀ p ∈ S, Nat.Prime p ∧ p % 4 = 3) ∧ Infinite S := sorry
