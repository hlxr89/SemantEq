import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem exercise_4_15 {f : ℝ → ℝ}
  (hf : Continuous f) (hof : IsOpenMap f) :
  Monotone f := sorry
