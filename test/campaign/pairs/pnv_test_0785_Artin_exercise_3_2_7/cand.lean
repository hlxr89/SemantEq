import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd RingHom
open scoped BigOperators

theorem dummy (F G : Type*) [Field F] [Field G] (f : F →+* G) : Function.Injective f := sorry
