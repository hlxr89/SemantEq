import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : UniformContinuous f) {x_n : ℕ → X} (hx : CauchySeq x_n) : CauchySeq (f ∘ x_n) := sorry
