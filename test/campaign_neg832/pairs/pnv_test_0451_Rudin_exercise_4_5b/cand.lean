import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (E : Set ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f E) (h : ¬∃ g : ℝ → ℝ, Continuous g ∧ ∀ x ∈ E, g x = f x) : ∃ ε : ℝ, ε > 0 ∧ ∀ δ : ℝ, δ > 0 → ∃ x ∈ E, ∀ y ∈ E, dist x y < δ → dist (f x) (f y) ≥ ε := sorry
