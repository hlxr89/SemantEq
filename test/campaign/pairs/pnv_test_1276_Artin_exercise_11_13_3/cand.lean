import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy : ∃ᶠ (p : ℕ) in atTop, p.Prime ∧ p % 4 = 3 := sorry
