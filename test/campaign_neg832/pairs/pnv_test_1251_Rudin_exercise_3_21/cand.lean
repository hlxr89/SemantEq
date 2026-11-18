import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type u} [MetricSpace X] [CompleteSpace X] {s : Set X} (hs : IsClosed s) (H : ∀ x ∈ s, 𝓝[s] x ≠ ⊥) : ∃ x ∈ s, s ⊆ closure ({x} : Set X) := sorry
