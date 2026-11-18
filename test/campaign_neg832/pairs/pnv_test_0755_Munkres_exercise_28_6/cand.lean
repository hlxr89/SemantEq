import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

theorem dummy {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → X} (hf : Isometry f) : Function.Bijective f := sorry
