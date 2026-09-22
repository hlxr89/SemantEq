import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_13b_assumed {f : ℂ → ℂ} (Ω : Set ℂ) (a b : Ω) (h : IsOpen Ω)
  (hf : DifferentiableOn ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).im = c) :
  f a = f b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {Ω : Set ℂ} (hf : IsOpen Ω) (f : ℂ → ℂ) (hf_holo : ∀ z ∈ Ω, DifferentiableAt ℂ f z) (h_im_const : ∃ c : ℝ, ∀ z ∈ Ω, (f z).im = c) : ∃ c : ℂ, ∀ z ∈ Ω, f z = c := by
  by_cases hΩ : Ω.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hΩ
    refine ⟨f z₀, ?_⟩
    intro z hz
    exact exercise_1_13b_assumed Ω ⟨z, hz⟩ ⟨z₀, hz₀⟩ hf
      (fun w hw ↦ (hf_holo w hw).differentiableWithinAt) h_im_const
  · refine ⟨0, ?_⟩
    intro z hz
    exact (hΩ ⟨z, hz⟩).elim
