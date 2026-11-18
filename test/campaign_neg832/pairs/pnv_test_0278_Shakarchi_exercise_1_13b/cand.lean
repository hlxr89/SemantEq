import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hf_diff : DifferentiableOn ℂ f s) (hf_im : ∀ z, z ∈ s → f z = f z) : ∀ z w, z ∈ s → w ∈ s → f z = f w := sorry
