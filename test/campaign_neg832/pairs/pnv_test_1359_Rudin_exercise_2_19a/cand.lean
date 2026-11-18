import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) : ∃ (ε : ℝ), ε > 0 ∧ ∀ (x : X), x ∈ A → ∀ (y : X), y ∈ B → dist x y ≥ ε := sorry
