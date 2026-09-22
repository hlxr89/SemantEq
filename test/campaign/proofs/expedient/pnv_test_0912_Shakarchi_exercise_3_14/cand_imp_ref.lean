import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℂ → ℂ) (hf_entire : Differentiable ℂ f) (hf_injective : Function.Injective f) : ∃ (a b : ℂ), a ≠ 0 ∧ ∀ z : ℂ, f z = a * z + b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_14 {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_inj : Function.Injective f) :
    ∃ (a b : ℂ), f = (λ z => a * z + b) ∧ a ≠ 0 := by
  rcases dummy_assumed f hf hf_inj with ⟨a, b, ha, hab⟩
  refine ⟨a, b, ?_, ha⟩
  funext z
  exact hab z
