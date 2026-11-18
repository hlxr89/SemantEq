import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy [TopologicalSpace X] [CompactSpace X] (f : X → X) (hf : Continuous f) : ∃ x : X, f x = x := sorry
