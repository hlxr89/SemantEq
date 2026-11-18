import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} (hf : ContDiff ℝ (↑1) f) {x₀ : E} (hx₀ : f x₀ = x₀) (h : ∀ (δ : ℝ), δ > 0 → ∀ (y : E), dist y x₀ < δ → dist (f y) (f x₀) > 0) (ε : ℝ) : ∃ (hε : ε > 0) (δ : ℝ), δ > 0 ∧ ∀ (x : E), dist x x₀ < δ → dist (f x) x₀ < ε := sorry
