import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {a : F} {v : V} (h : a • v = 0) : a = 0 ∨ v = 0 := sorry
