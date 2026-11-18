import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf : UniformContinuousOn f (Set.Icc (-4) 4)) : ContinuousOn f (Set.Icc (-4) 4) := sorry
