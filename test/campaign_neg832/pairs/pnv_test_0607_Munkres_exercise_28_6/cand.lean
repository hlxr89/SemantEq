import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

theorem dummy {X : Type u} [MetricSpace X] (f : X → X) (hf : ∀ x y : X, dist (f x) (f y) = dist x y) (hX : CompactSpace X) : Function.Bijective f := sorry
