import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (f : ℝ → ℝ) (hf : Continuous f) (hf_open : IsOpenMap f) : Monotone f := sorry
