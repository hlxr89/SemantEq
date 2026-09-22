import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy : ∃ (E : Set ℝ) (f : ℝ → ℝ), ContinuousOn f E ∧ ¬(∃ g : ℝ → ℝ, Continuous g ∧ ∀ x ∈ E, g x = f x) := sorry
