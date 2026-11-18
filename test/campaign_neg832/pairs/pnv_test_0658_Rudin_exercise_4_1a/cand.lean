import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (f : ℝ → ℝ) (hf : ∀ x, Tendsto (fun h => f (x + h) - f (x - h)) (𝓝[>] 0) (𝓝 0)) : ∃ x, ¬Tendsto (deriv f) (𝓝 x) (𝓝 (deriv f x)) := sorry
