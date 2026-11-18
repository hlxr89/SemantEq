import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOn ℂ f U) (h : ∀ x ∈ U, (f x).im = 0) : ∀ x ∈ U, f x = x := sorry
