import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy [TopologicalSpace X] (f : X → ℝ) (hc : Continuous f) : IsClosed {x : X | f x = 0} := sorry
