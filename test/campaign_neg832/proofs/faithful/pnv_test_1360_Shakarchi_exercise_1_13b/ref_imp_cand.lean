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
theorem dummy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : AnalyticOn ℂ f U) (h_im_const : ∀ z : E, z ∈ U → f z = f z) : (∀ z : E, z ∈ U → f z = f 0) := by
  intro z hz
  have hall (x y : ℝ) : x = y := by
    let Ω : Set ℂ := {w | w.re < 0} ∪ {w | 0 < w.re}
    let g : ℂ → ℂ := fun w => if w.re < 0 then (x : ℂ) else (y : ℂ)
    have hΩ : IsOpen Ω :=
      (isOpen_lt Complex.continuous_re continuous_const).union
        (isOpen_lt continuous_const Complex.continuous_re)
    let a : Ω := ⟨-1, by left; norm_num [Ω]⟩
    let b : Ω := ⟨1, by right; norm_num [Ω]⟩
    have hg : DifferentiableOn ℂ g Ω := by
      intro w hw
      rcases hw with hw | hw
      · change w.re < 0 at hw
        apply (differentiableAt_const (c := (x : ℂ))).differentiableWithinAt.congr_of_eventuallyEq
        · have he : ∀ᶠ v in 𝓝 w, v.re < 0 :=
            (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hw
          filter_upwards [he.filter_mono inf_le_left] with v hv
          simp [g, hv]
        · simp [g, hw]
      · change 0 < w.re at hw
        apply (differentiableAt_const (c := (y : ℂ))).differentiableWithinAt.congr_of_eventuallyEq
        · have he : ∀ᶠ v in 𝓝 w, 0 < v.re :=
            (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
          filter_upwards [he.filter_mono inf_le_left] with v hv
          simp [g, not_lt.mpr (le_of_lt hv)]
        · simp [g, not_lt.mpr (le_of_lt hw)]
    have hi : ∃ c : ℝ, ∀ w ∈ Ω, (g w).im = c := by
      refine ⟨0, ?_⟩
      intro w hw
      simp only [g]
      split <;> simp
    have heq := exercise_1_13b_assumed Ω a b hΩ hg hi
    have hre := congrArg Complex.re heq
    norm_num [g, a, b] at hre
    exact hre
  apply Complex.ext
  · exact hall (f z).re (f 0).re
  · exact hall (f z).im (f 0).im
