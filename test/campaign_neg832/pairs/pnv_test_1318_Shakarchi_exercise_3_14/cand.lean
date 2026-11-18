import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {f : ℂ → ℂ} (hf : ∀ zᵢ zₒ, zᵢ ≠ zₒ → f zᵢ ≠ f zₒ) : ∃ (a b : ℂ), f z = a * z + b := sorry
