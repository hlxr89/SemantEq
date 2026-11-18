import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℂ → ℂ} (hf : ∀ zᵢ zₒ, zᵢ ≠ zₒ → f zᵢ ≠ f zₒ) : ∃ (a b : ℂ), f z = a * z + b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_14 {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_inj : Function.Injective f) :
    ∃ (a b : ℂ), f = (λ z => a * z + b) ∧ a ≠ 0 := by
  -- not proved: dummy_assumed supplies an affine equation at only one implicit point, not a global function identity or a ≠ 0
  sorry
