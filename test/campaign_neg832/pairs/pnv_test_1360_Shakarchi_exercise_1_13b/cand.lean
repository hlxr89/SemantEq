import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem dummy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : AnalyticOn ℂ f U) (h_im_const : ∀ z : E, z ∈ U → f z = f z) : (∀ z : E, z ∈ U → f z = f 0) := sorry
