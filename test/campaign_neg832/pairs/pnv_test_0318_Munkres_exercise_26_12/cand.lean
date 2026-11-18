import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (hX : T2Space X) (p : X → Y) (h_cont : Continuous p) (h_surj : Function.Surjective p) (h_closed : IsClosedMap p) (h_compact_fibers : ∀ y : Y, IsCompact (p ⁻¹' {y})) : CompactSpace X := sorry
