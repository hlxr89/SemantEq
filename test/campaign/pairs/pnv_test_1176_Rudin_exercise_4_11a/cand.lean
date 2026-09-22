import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : UniformContinuous f) {xn : ℕ → X} (hxn : CauchySeq xn) : CauchySeq (f ∘ xn) := sorry
