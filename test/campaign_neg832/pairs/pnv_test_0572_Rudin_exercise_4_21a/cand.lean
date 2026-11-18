import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy [PseudoMetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (hd : Disjoint K F) : ∃ (δ : ℝ) (H : δ > 0), ∀ {x y : X}, x ∈ K → y ∈ F → dist x y > δ := sorry
