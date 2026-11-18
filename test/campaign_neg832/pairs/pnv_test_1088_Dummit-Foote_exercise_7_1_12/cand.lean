import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {F : Type u} [Field F] {R : Type u} [Ring R] (f : R →+* F) (hf1 : f 1 = 1) (hf3 : Function.Surjective f) : IsDomain R := sorry
