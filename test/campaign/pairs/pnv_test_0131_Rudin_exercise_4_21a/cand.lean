import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) : ∃ ε : ℝ, ε > 0 ∧ ∀ (p : X) (hp : p ∈ K) (q : X) (hq : q ∈ F), dist p q ≥ ε := sorry
