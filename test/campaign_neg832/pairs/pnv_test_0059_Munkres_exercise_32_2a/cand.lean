import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {α : Type*} {X : α → Type*} [∀ a, TopologicalSpace (X a)] (h : TopologicalSpace (Π a, X a)) (hH : T2Space (Π a, X a)) (a : α) : T2Space (X a) := sorry
