import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {α : Type u} {X : α → Type v} [∀ a : α, TopologicalSpace (X a)] [∀ (a : α), T2Space (X a)] : T2Space (∀ a, X a) := sorry
