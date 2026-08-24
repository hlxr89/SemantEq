import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [NormalSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) : ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ U ⊆ A ∧ V ⊆ B ∧ closure U ∩ closure V = ∅ := sorry
