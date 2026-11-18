import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {E : Set ℝ} (hE : E.Nonempty) {f : ℝ → ℝ} (hf : Continuous f): ∃ (hE' : E ⊆ Set.univ), ¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ (x : ℝ), x ∈ E → g x = f x := sorry
