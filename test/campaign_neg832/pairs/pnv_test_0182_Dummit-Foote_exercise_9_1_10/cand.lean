import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] : ∃ (f : R[X]) (hf : ∀ i : ℕ, f.degree ≠ 2*i), ∃ (P : Ideal (R[X])), Ideal.IsPrime P ∧ Ideal.IsMaximal P := sorry
