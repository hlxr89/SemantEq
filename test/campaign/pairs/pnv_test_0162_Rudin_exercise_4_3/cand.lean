import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] {f : X → ℝ} (hf : Continuous f) : IsClosed {p : X | f p = 0} := sorry
