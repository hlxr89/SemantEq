import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy : ∃ f : ℕ → ℕ, ∀ n : ℕ, 1 ≤ n → ((f n : ℤ) % 4 = -1) ∧ Prime (f n) := sorry
