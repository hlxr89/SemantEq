import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] [T2Space X] (p : X → Y) (hc : Continuous p) (hs : Function.Surjective p) (hk : ∀ y : Y, IsCompact (p ⁻¹' {y})) : CompactSpace X := sorry
