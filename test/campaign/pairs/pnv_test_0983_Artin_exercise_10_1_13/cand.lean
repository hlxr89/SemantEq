import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {R : Type*} [Ring R] (x : R) (h : ∃ n : ℕ, x ^ n = 0) : IsUnit (1 + x) := sorry
