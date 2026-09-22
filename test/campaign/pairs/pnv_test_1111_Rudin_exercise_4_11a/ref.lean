import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem exercise_4_11a
  {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y]
  (f : X → Y) (hf : UniformContinuous f)
  (x : ℕ → X) (hx : CauchySeq x) :
  CauchySeq (λ n => f (x n)) := sorry
