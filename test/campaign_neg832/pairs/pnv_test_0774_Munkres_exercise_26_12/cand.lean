import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] (f : X → Y) (hf : Continuous f) (hf2 : Function.Surjective f) (hf3 : ∀ y : Y, IsCompact (f⁻¹' {y}) ) : CompactSpace X := sorry
