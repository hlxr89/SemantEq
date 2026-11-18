import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {s1 s2 : Submodule K V} : s1 ⊔ s2 = ⊤ ↔ s1 ≤ s2 ∨ s2 ≤ s1 := sorry
