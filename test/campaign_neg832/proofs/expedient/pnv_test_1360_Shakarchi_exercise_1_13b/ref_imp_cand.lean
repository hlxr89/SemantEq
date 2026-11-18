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
  exfalso
  let Ω : Set ℂ := {z | z.re < 0} ∪ {z | 0 < z.re}
  let g : ℂ → ℂ := fun z ↦ if z.re < 0 then 0 else 1
  have hΩ : IsOpen Ω := by
    dsimp [Ω]
    exact (isOpen_lt continuous_re continuous_const).union
      (isOpen_lt continuous_const continuous_re)
  have hg : DifferentiableOn ℂ g Ω := by
    intro z hz
    rcases hz with hz | hz
    · change z.re < 0 at hz
      have he : ∀ᶠ w in 𝓝 z, w.re < 0 :=
        (isOpen_lt continuous_re continuous_const).eventually_mem hz
      refine ((differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [he] with w hw
      simp [g, hw]
    · change 0 < z.re at hz
      have he : ∀ᶠ w in 𝓝 z, 0 < w.re :=
        (isOpen_lt continuous_const continuous_re).eventually_mem hz
      refine ((differentiableAt_const (c := (1 : ℂ))).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [he] with w hw
      simp [g, not_lt.mpr hw.le]
  have hc : ∃ (c : ℝ), ∀ z ∈ Ω, (g z).im = c := by
    refine ⟨0, ?_⟩
    intro z hz
    by_cases hz0 : z.re < 0 <;> simp [g, hz0]
  let a : Ω := ⟨-1, Or.inl (by norm_num)⟩
  let b : Ω := ⟨1, Or.inr (by norm_num)⟩
  have hab := exercise_1_13b_assumed Ω a b hΩ hg hc
  norm_num [g, a, b] at hab
