import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {A : Set X} (hA : IsClosed A) {f g : X → Y} (hf : ContinuousOn f A) (hg : ContinuousOn g A) (h : EqOn f g A) (h' : EqOn f g (closure A)) : f = g := sorry
