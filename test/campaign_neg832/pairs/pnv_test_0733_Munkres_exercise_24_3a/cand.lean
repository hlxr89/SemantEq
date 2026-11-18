import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {f : X → X} (hf : Continuous f) : ∃ x : X, f x = x := sorry
