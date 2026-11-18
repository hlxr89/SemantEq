import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] [CompactSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) : ∃ (ε : ℝ), ε > 0 ∧ ∀ a ∈ A, ∀ b ∈ B, dist a b ≥ ε := sorry
