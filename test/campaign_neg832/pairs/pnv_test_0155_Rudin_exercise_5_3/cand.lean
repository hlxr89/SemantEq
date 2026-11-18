import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} {f' : ℝ → ℝ} {g : ℝ → ℝ} {g' : ℝ → ℝ} {a x : ℝ} (hderiv : ∀ x, HasDerivAt f (f' x) x) (hderivg : ∀ x, HasDerivAt g (g' x) x) (hx : x ∈ Metric.ball a 1) (hM : ∀ x, ‖f' x‖ ≤ M) (hgM : ∀ x, ‖g' x‖ ≤ M) : x ∈ Metric.ball a ‖ε * M‖ := sorry
