import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Set
open scoped BigOperators

theorem dummy {X : Type*} [NormedAddCommGroup X] (f : ℝ → X) (g : ℝ → X) (h : ∀ x, dist (f x) (g x) ≤ 1) : Tendsto (fun x => f x - g x) atTop (𝓝 0) := sorry
