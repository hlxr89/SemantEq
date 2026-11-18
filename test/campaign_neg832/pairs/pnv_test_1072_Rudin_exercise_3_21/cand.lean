import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type u} [MetricSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (h's : Set.Nonempty s) (h't : Set.Nonempty t) : (∃ x ∈ s, ∃ y ∈ t, x = y) ↔ s = t := sorry
