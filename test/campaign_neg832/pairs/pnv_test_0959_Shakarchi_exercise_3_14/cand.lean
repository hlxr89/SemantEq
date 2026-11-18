import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {f : ℂ → ℂ} (hf : ∀ z : ℂ, f z ≠ 0) : ∃ (a b : ℂ), a ≠ 0 ∧ ∀ z, f z = a * z + b := sorry
