import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (a b : R) : a ∈ Submodule.span R {b} ↔ b ∈ Submodule.span R {a} := sorry
