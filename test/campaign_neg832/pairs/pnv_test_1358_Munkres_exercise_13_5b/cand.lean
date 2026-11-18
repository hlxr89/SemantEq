import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} (A : Set (Set X)) : generateFrom A = ⨅ (T : TopologicalSpace X) (hT : ∀ a ∈ A, IsOpen a), T := sorry
