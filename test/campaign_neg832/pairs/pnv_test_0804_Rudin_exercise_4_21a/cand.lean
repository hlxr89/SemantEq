import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type u} [MetricSpace X] [Nonempty X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (h : K ∩ F = ∅) : ∃ δ : ℝ, δ > 0 ∧ ∀ (p : X) (q : X), p ∈ K → q ∈ F → dist p q ≥ δ := sorry
