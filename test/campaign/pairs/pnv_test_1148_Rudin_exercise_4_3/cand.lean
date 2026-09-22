import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy [MetricSpace X] [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f) : IsClosed (f ⁻¹' {0}) := sorry
