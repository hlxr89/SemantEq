import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd RingHom
open scoped BigOperators

theorem dummy {K L : Type*} [Field K] [Field L] (f : K →+* L) : Function.Injective f := sorry
