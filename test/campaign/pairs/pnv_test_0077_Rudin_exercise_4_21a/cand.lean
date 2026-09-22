import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] {K F : Set X} (hK : CompactSpace K) (hF : IsClosed F) (hKF : Disjoint K F) : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K, ∀ q ∈ F, dist p q > δ := sorry
