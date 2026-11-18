import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (h : ∀ x, Tendsto (fun h => f (x + h) - f (x - h)) (𝓝 0) (𝓝 0)) : ¬Continuous f := sorry
