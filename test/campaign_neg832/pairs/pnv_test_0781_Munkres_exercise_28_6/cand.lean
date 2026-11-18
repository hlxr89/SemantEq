import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

theorem dummy {X : Type u} [MetricSpace X] [CompactSpace X] {f : X → X} (h : ∀ x y : X, dist (f x) (f y) = dist x y) : Isometry f := sorry
