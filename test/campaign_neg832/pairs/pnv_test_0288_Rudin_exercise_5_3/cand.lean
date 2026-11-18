import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (f' : ℝ → ℝ) (hf' : ∀ x, ‖f' x‖ ≤ M) (hε : 0 < ε ∧ ε ≤ M⁻¹) : Function.Injective (λ x => x + ε * f x) := sorry
