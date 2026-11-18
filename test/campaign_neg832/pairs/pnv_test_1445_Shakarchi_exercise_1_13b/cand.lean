import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {f : ℂ → ℂ} {s : Set ℂ} (hf : AnalyticOn ℂ f s) : (∀ z ∈ s, (f z).im = (f z₀).im) → ∀ z ∈ s, f z = f z₀ := sorry
