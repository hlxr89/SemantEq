import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊥) : ∃ (x : R), x ≠ 0 ∧ x ∉ I := sorry
