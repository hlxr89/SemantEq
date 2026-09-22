import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (f : ℝ → ℝ) (hc : Continuous f) (ho : IsOpenMap f) : Monotone f := sorry
