import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f) (hf_injective : Function.Injective f) : ∃ (a b : ℂ), a ≠ 0 ∧ ∀ z, f z = a * z + b := sorry
