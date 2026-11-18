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
theorem dummy {f : ℂ → ℂ} {s : Set ℂ} (hf : AnalyticOn ℂ f s) : (∀ z ∈ s, (f z).im = (f z₀).im) → ∀ z ∈ s, f z = f z₀ := by
  intro him z hz
  let Ω : Set ℂ := {w | w.re ≠ 0}
  let g : ℂ → ℂ := fun w => if w.re < 0 then f z else f z₀
  have hΩ : IsOpen Ω := isOpen_compl_singleton.preimage continuous_re
  have hg : DifferentiableOn ℂ g Ω := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    by_cases hn : w.re < 0
    · have he : ∀ᶠ x in 𝓝 w, x.re < 0 :=
        (continuous_re.tendsto w).eventually (Iio_mem_nhds hn)
      apply (differentiableAt_const (𝕜 := ℂ) (f z)).congr_of_eventuallyEq
      filter_upwards [he] with x hx
      simp [g, hx]
    · have hp : 0 < w.re := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hw)
      have he : ∀ᶠ x in 𝓝 w, 0 ≤ x.re :=
        (continuous_re.tendsto w).eventually (Ici_mem_nhds hp)
      apply (differentiableAt_const (𝕜 := ℂ) (f z₀)).congr_of_eventuallyEq
      filter_upwards [he] with x hx
      simp [g, not_lt.mpr hx]
  have him' : (f z).im = (f z₀).im := him z hz
  have hc : ∃ (c : ℝ), ∀ w ∈ Ω, (g w).im = c := by
    refine ⟨(f z₀).im, ?_⟩
    intro w hw
    by_cases hn : w.re < 0
    · simpa [g, hn] using him'
    · simp [g, hn]
  have h := exercise_1_13b_assumed Ω (⟨-1, by simp [Ω]⟩ : Ω)
    (⟨1, by simp [Ω]⟩ : Ω) hΩ hg hc
  simpa [g] using h
