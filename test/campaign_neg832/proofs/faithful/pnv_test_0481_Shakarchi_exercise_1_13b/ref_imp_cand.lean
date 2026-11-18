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
theorem dummy {f : ℂ → ℂ} {s : Set ℂ} (hf : AnalyticOn ℂ f s) (hc : ∀ z ∈ s, (f z).im = 0) : ∀ z ∈ s, f z = const ℂ (f 0) z := by
  have allRealEqual : ∀ x y : ℝ, x = y := by
    intro x y
    let Ω : Set ℂ := {w | w.re < 0} ∪ {w | 0 < w.re}
    let a : Ω := ⟨-1, by left; norm_num⟩
    let b : Ω := ⟨1, by right; norm_num⟩
    let g : ℂ → ℂ := fun w => if w.re < 0 then (x : ℂ) else (y : ℂ)
    have hΩ : IsOpen Ω := by
      exact (isOpen_lt continuous_re continuous_const).union
        (isOpen_lt continuous_const continuous_re)
    have hg : DifferentiableOn ℂ g Ω := by
      intro w hw
      rcases hw with hw | hw
      · change w.re < 0 at hw
        have he : ∀ᶠ u in 𝓝 w, u.re < 0 :=
          (isOpen_lt continuous_re continuous_const).mem_nhds hw
        have he' : ∀ᶠ u in 𝓝[Ω] w, u.re < 0 :=
          he.filter_mono inf_le_left
        apply (differentiableAt_const (c := (x : ℂ))).differentiableWithinAt.congr_of_eventuallyEq
        · filter_upwards [he'] with u hu
          simp [g, hu]
        · change (if w.re < 0 then (x : ℂ) else (y : ℂ)) = (x : ℂ)
          rw [if_pos hw]
      · change 0 < w.re at hw
        have he : ∀ᶠ u in 𝓝 w, 0 < u.re :=
          (isOpen_lt continuous_const continuous_re).mem_nhds hw
        have he' : ∀ᶠ u in 𝓝[Ω] w, 0 < u.re :=
          he.filter_mono inf_le_left
        apply (differentiableAt_const (c := (y : ℂ))).differentiableWithinAt.congr_of_eventuallyEq
        · filter_upwards [he'] with u hu
          simp [g, not_lt_of_ge (le_of_lt hu)]
        · change (if w.re < 0 then (x : ℂ) else (y : ℂ)) = (y : ℂ)
          rw [if_neg (not_lt_of_ge (le_of_lt hw))]
    have hgi : ∃ (c : ℝ), ∀ z ∈ Ω, (g z).im = c := by
      refine ⟨0, ?_⟩
      intro z hz
      simp only [g]
      split_ifs <;> simp
    have hxy := exercise_1_13b_assumed (f := g) Ω a b hΩ hg hgi
    have hxy' : (x : ℂ) = (y : ℂ) := by
      simpa [g, a, b] using hxy
    simpa using congrArg Complex.re hxy'
  intro z hz
  apply Complex.ext
  · exact allRealEqual (f z).re (const ℂ (f 0) z).re
  · exact allRealEqual (f z).im (const ℂ (f 0) z).im
