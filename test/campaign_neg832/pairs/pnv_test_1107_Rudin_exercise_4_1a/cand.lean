import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf : ∀ (x : ℝ), Tendsto (fun h => f (x + h) - f (x - h)) (𝓝 0) (𝓝 0)) : Tendsto f (𝓝 0) (𝓝 0) := sorry
