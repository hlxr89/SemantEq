import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M] {v : M} {a : R} (h : a • v = 0) : a = 0 ∨ v = 0 := sorry
