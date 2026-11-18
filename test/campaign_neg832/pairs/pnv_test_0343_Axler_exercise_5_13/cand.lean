import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {α : Type u} [CompleteLattice α] {ι : Sort u_1} {f : ι → α} : ⨆ (i : ι) (hi : True), f i = ⨅ (i : ι) (hi : True), f i := sorry
