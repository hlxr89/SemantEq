import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {I : Ideal ℤ} (hI : I ≠ ⊥) : ∃ (n : ℤ), n ≠ 0 ∧ n ∈ I := sorry
