import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (f : ℝ → ℝ) (hf : ∀ (x : ℝ), ∃ (h : ℝ), ∀ (h0 : 0 < h), |f (x + h) - f x| < h) (h : ¬ UniformContinuous f) : ∃ x : ℝ, ContinuousAt f x := sorry
