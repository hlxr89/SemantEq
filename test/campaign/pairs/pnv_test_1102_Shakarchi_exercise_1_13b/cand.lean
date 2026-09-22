import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {Ω : Set ℂ} (h : IsOpen Ω) {f : ℂ → ℂ} (hf : AnalyticOn ℂ f Ω) (hc : ∀ z ∈ Ω, (f z).im = (f 0).im) : (∀ z ∈ Ω, f z = f 0) := sorry
