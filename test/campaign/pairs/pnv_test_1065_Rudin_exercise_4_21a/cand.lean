import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (h : Disjoint K F) : ∃ (δ : ℝ) (H : 0 < δ), ∀ {p q : X}, p ∈ K → q ∈ F → dist p q > δ := sorry
