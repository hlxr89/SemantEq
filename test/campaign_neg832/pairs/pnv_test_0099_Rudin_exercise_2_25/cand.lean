import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] [CompactSpace X] : ∃ s : Set X, s.Countable ∧ ∀ x : X, ∃ y ∈ s, dist x y < 1 := sorry
