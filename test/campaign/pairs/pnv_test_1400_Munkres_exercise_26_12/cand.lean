import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp_closed : IsClosedMap p) (hp_cont : Continuous p) (hp_surj : Function.Surjective p) (hp_preimage_compact : ∀ y, IsCompact (p ⁻¹' {y})) (hY : CompactSpace Y) : CompactSpace X := sorry
