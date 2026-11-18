import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {f : ℝ → ℝ} (hf : Differentiable ℝ f) {M : ℝ} (h : ∀ x, 0 ≤ x → 0 ≤ deriv f x ∧ deriv f x ≤ M) : ∃ ε, 0 < ε ∧ ∀ x, ε ≤ x → 0 ≤ x := sorry
