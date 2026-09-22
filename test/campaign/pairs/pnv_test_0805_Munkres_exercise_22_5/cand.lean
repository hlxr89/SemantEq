import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : IsOpenMap f) (A : Set X) : IsOpenMap (Set.restrict A f) := sorry
