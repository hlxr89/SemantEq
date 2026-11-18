import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X α : Type} [tα : Nonempty α] {f : α → Type} [Π a, TopologicalSpace (f a)] [∀ a, NormalSpace (f a)] (h : NormalSpace (∀ a, f a)): ∀ a, NormalSpace (f a) := sorry
