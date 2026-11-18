import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {α : Type*} {X : α → Type*} [∀ a, TopologicalSpace (X a)] [h : NormalSpace (Π a, X a)] (a : α) [Nonempty (X a)] : NormalSpace (X a) := sorry
