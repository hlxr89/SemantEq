import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (h : CompactSpace Y) (h' : Continuous p) (h'' : Function.Surjective p) (hc : ∀ y : Y, IsCompact (p ⁻¹' {y})) : CompactSpace X := sorry
