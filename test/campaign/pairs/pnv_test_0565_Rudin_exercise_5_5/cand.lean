import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Set
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf : ∀ x > 0, DifferentiableAt ℝ f x) (hf' : Tendsto (fun x => deriv f x) atTop (𝓝 0)) : Tendsto (fun x => f (x + 1) - f x) atTop (𝓝 0) := sorry
