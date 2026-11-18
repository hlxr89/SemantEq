import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (g : ℝ → ℝ) (g'bound : ∀ x : ℝ, ‖deriv g x‖ ≤ 1) (hε : 0 < ε) (h : ∀ x y : ℝ, x ≠ y → ‖g x - g y‖ ≥ ε * ‖x - y‖) : Function.Injective fun x ↦ x + ε * g x := sorry
