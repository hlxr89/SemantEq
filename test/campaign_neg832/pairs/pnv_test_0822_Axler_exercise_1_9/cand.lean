import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M] (X Y : Submodule R M) (hXY : X ≤ Y) : X ⊔ Y = Y := sorry
