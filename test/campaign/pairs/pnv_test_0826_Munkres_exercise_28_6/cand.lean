import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

theorem dummy {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, dist (f x) (f y) = dist x y) : Function.Bijective f ∧ ∃ h : Homeomorph X X, h.toFun = f := sorry
