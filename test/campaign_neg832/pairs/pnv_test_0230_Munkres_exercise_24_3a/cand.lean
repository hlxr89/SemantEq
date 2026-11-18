import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy [MetricSpace X] (f : X → X) (hf : Continuous f) (hX : (0 : ℝ) < 1) : ∃ x, f x = x := sorry
