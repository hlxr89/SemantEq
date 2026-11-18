import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (E : Set ℝ) : ∃ (f : ℝ → ℝ)(Hf : ContinuousOn f E), ∀ (g : ℝ → ℝ), g =ᶠ[𝓝ˢ E] f → ¬Continuous g := sorry
