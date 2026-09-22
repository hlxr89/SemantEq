import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [MetricSpace X] {f : X → ℝ} (hf : Continuous f) : IsClosed {x : X | f x = 0} := sorry
