import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M] (a : R) (v : M) (h : a • v = 0) : a = 0 ∨ v = 0 := sorry
