import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (hY : T2Space Y) {A : Set X} (hA : IsClosed (A : Set X)) {f : A → Y} (hf : Continuous f) : ∃! (g : X → Y), (∀ a : A, g a = f a) ∧ Continuous g := sorry
