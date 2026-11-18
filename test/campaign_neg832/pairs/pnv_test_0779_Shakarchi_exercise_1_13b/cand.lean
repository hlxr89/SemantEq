import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {f : ℂ → ℂ} {n : ℕ} (hn : 0 < n) (hf : HasDerivAt f (0 : ℂ) 0) : f = const ℂ 0 := sorry
