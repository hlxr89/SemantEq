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
  have real_eq (x y : ℝ) : x = y := by
    let Ω : Set ℂ := {z | z.re < 0} ∪ {z | 0 < z.re}
    let g : ℂ → ℂ := fun z => if z.re < 0 then (x : ℂ) else (y : ℂ)
    have hΩ : IsOpen Ω := by
      exact (isOpen_lt continuous_re continuous_const).union
        (isOpen_lt continuous_const continuous_re)
    have hg : DifferentiableOn ℂ g Ω := by
      intro z hz
      change z.re < 0 ∨ 0 < z.re at hz
      rcases hz with hz | hz
      · apply DifferentiableAt.differentiableWithinAt
        apply (differentiableAt_const (c := (x : ℂ))).congr_of_eventuallyEq
        filter_upwards [(isOpen_lt continuous_re continuous_const).eventually_mem hz] with w hw
        simp only [g, if_pos hw]
      · apply DifferentiableAt.differentiableWithinAt
        apply (differentiableAt_const (c := (y : ℂ))).congr_of_eventuallyEq
        filter_upwards [(isOpen_lt continuous_const continuous_re).eventually_mem hz] with w hw
        simp only [g, if_neg (not_lt.mpr (le_of_lt hw))]
    let a : Ω := ⟨-1, by
      left
      change (-1 : ℝ) < 0
      exact neg_lt_zero.mpr zero_lt_one⟩
    let b : Ω := ⟨1, by
      right
      change (0 : ℝ) < 1
      exact zero_lt_one⟩
    have heq := exercise_1_13b_assumed Ω a b hΩ hg
      ⟨0, fun z hz => by
        change z.re < 0 ∨ 0 < z.re at hz
        rcases hz with hz | hz
        · simp only [g, if_pos hz, Complex.ofReal_im]
        · simp only [g, if_neg (not_lt.mpr (le_of_lt hz)), Complex.ofReal_im]⟩
    have hre := congrArg Complex.re heq
    simpa only [a, b, g, Complex.neg_re, Complex.one_re,
      if_pos (neg_lt_zero.mpr zero_lt_one), if_neg (not_lt.mpr zero_le_one),
      Complex.ofReal_re] using hre
  intro z hz
  change f z = f 0
  apply Complex.ext
  · exact real_eq (f z).re (f 0).re
  · rw [hc z hz, real_eq (f 0).im 0]
