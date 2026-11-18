import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} (T : TopologicalSpace X) (A : Set (Set X)) (hA : IsTopologicalBasis A) : T = generateFrom A := sorry
