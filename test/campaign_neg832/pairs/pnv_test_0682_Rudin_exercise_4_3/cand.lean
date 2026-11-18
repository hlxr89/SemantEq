import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] [T2Space X] {f : X → ℝ} (hf : Continuous f): IsClosed {p | f p = 0} := sorry
