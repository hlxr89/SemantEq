import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {Ω : Set ℂ} (hf : IsOpen Ω) (f : ℂ → ℂ) (hf_holo : ∀ z ∈ Ω, DifferentiableAt ℂ f z) (h_im_const : ∃ c : ℝ, ∀ z ∈ Ω, (f z).im = c) : ∃ c : ℂ, ∀ z ∈ Ω, f z = c := sorry
