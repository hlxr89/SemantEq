import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {A : Set X} (hA : IsClosed A) {f : X → Y} (hf : ContinuousOn f A) {g₁ g₂ : X → Y} (hg₁ : ContinuousOn g₁ (closure A)) (hg₂ : ContinuousOn g₂ (closure A)) (hgf₁ : EqOn g₁ f A) (hgf₂ : EqOn g₂ f A) : EqOn g₁ g₂ (closure A) := sorry
