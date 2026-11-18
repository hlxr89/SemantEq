import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {S T : Submodule K V} : S ⊔ T = S ∨ S ⊔ T = T := sorry
