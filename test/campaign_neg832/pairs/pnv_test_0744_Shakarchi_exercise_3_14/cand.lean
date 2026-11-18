import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {f : ℂ → ℂ} (hf : ∀ z : ℂ, (∃ w : ℂ, f w = z) → z = f z) : ∃ a b : ℂ, f z = a * z + b := sorry
