import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {A : Set X} {f : X → Y} (hA : IsClosed A) (hf : ContinuousOn f A) (hf' : ∀ x : X, x ∈ A → ContinuousWithinAt f A x) : ∃! g : X → Y, Continuous g ∧ EqOn f g A := sorry
