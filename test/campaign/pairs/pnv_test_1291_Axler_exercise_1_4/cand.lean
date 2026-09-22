import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (a : K) (v : V) (h : a • v = 0) : a = 0 ∨ v = 0 := sorry
