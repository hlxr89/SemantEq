import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (f : ℝ → ℝ) {s : Set ℝ} (hs : s.Countable) (hf : DifferentiableOn ℝ f s) (hf' : ∀ x ∈ s, DifferentiableAt ℝ f x) (hfd : ∀ x ∈ s, DifferentiableWithinAt ℝ (fderiv ℝ f x) s x) : ∃ C : ℝ, ∀ x ∈ s, ‖fderivWithin ℝ f s x‖ ≤ C := sorry
