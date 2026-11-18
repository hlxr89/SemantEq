import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type u} {τ : TopologicalSpace X} {B : Set (Set X)} (h : B ⊆ τ.IsOpen) : generateFrom B = ⨅ (l : TopologicalSpace X) (_ : B ⊆ l.IsOpen), l := sorry
