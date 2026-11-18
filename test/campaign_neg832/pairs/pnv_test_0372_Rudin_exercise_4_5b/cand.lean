import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (X : Type*) [TopologicalSpace X] (E : Set X) (f : X → ℝ) (hf : ContinuousOn f E) : ∃ (F : Set X) (g : X → ℝ), ContinuousOn g F ∧ F ⊆ E ∧ (∀ (x : X), x ∈ F → g x = f x) ∧ ¬ ∃ (g : X → ℝ), Continuous g ∧ ∀ (x : X), x ∈ E → g x = f x := sorry
