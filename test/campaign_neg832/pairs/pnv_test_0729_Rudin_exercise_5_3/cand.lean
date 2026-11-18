import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (g : ℝ → ℝ) (hbdd : ∀ x, ‖deriv g x‖ ≤ M) (ε : ℝ) (hε : ε * M < 1) : Function.Injective fun x => x + ε * g x := sorry
