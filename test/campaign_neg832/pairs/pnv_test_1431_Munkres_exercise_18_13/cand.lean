import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {A : Set X} (h : IsClosed (closure Aᶜ : Set X)) {f : X → Y} (hf : ContinuousOn f A) (g : X → Y) (hg : ContinuousOn g A) (hfg : Set.EqOn f g (closure Aᶜ)) : Set.EqOn f g A := sorry
