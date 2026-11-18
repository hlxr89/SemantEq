import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp : Continuous p) (hps : ∀ y, IsCompact (p ⁻¹' {y} : Set X)) (hY : CompactSpace Y) : CompactSpace X := sorry
