import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} {T : TopologicalSpace X} {B : Set (Set X)} (h : B ⊆ T.IsOpen) : TopologicalSpace.generateFrom B = ⨅ (S : TopologicalSpace X) (_ : B ⊆ S.IsOpen), S := sorry
