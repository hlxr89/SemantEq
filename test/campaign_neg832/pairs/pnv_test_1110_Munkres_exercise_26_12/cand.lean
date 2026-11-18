import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (hp : Continuous p) (hps : IsClosed (range p)) (hps_inv : ∀ y : Y, IsCompact (p ⁻¹' {y})) (hY : CompactSpace Y) : CompactSpace X := sorry
