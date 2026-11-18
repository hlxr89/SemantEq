import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {E : Set ℝ} (hE : BddAbove E) (f : ℝ → ℝ) (hf : UniformContinuous f) (hfE : ∀ x ∈ E, f x ∈ E) : BddAbove (f '' E) := sorry
