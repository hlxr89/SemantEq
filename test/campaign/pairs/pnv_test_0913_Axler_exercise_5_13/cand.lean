import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : End K V) (h : ∀ (U : Subspace K V), finrank K V - 1 = finrank K U → T '' U ≤ U) : ∃ (c : K), T = c • 1 := sorry
