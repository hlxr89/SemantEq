import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy : ∃ (s : Set ℝ) (f : ℝ → ℝ), Continuous f ∧ (∀ (x : ℝ), x ∈ s → f x = x) ∧ ¬ ∃ (g : ℝ → ℝ) (hg : Continuous g), ∀ (x : ℝ), x ∈ s → g x = f x := sorry
