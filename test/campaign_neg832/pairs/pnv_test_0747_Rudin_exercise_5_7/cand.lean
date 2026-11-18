import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X : Type*} [TopologicalSpace X] [LinearOrder X] [OrderTopology X] {f g : ℝ → ℝ} {a : ℝ} (f' : ℝ → ℝ) (g' : ℝ → ℝ) (hff' : ∀ x ≠ a, HasDerivAt f (f' x) x) (hg' : ∀ x ≠ a, HasDerivAt g (g' x) x) (hfa : f a = 0) (hga : g a = 0) (hg'_ne : ∀ x ≠ a, g' x ≠ 0) : Tendsto (fun t => (f t) / (g t)) (𝓝 a) (𝓝 (f' a / g' a)) := sorry
