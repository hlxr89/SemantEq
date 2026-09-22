import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Set
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (f_diff : ∀ x : ℝ, x > 0 → DifferentiableAt ℝ f x) (f_diff_zero : ∀ x : ℝ, x > 0 → HasDerivAt f (f' x) x) (hf' : Tendsto f' atTop (𝓝 0)) : Tendsto (fun x => f (x + 1) - f x) atTop (𝓝 0) := sorry
