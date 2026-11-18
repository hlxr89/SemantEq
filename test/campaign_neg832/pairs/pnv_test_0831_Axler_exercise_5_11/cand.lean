import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {S T : Module.End K V} : S.eigenspace = T.eigenspace := sorry
