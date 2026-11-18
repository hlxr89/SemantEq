import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] {A B : Set X} (hAB : Disjoint A B) (hA : IsClosed A) (hB : IsClosed B): ∃ (ε : ℝ), ε > 0 ∧ ∀ x ∈ A, ∀ y ∈ B, dist x y ≥ ε := sorry
