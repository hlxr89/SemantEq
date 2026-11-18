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
  have h_re : ∀ x y : ℂ, x.re = y.re := by
    intro x y
    let V : Set ℂ := {w | w.re < 0} ∪ {w | 0 < w.re}
    let g : ℂ → ℂ := fun w => if w.re < 0 then (x.re : ℂ) else (y.re : ℂ)
    have hneg : IsOpen {w : ℂ | w.re < 0} :=
      isOpen_lt Complex.continuous_re continuous_const
    have hpos : IsOpen {w : ℂ | 0 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hV : IsOpen V := hneg.union hpos
    have hminus : (-1 : ℂ) ∈ V := by
      left
      norm_num
    have hplus : (1 : ℂ) ∈ V := by
      right
      norm_num
    have hg : DifferentiableOn ℂ g V := by
      intro w hw
      rcases hw with hw | hw
      · apply DifferentiableAt.differentiableWithinAt
        apply (differentiableAt_const (x.re : ℂ)).congr_of_eventuallyEq
        filter_upwards [hneg.eventually_mem hw] with v hv
        simp only [g, if_pos hv]
      · apply DifferentiableAt.differentiableWithinAt
        apply (differentiableAt_const (y.re : ℂ)).congr_of_eventuallyEq
        filter_upwards [hpos.eventually_mem hw] with v hv
        have hv' : ¬v.re < 0 := not_lt.mpr (le_of_lt hv)
        simp only [g, if_neg hv']
    have him : ∃ (c : ℝ), ∀ w ∈ V, (g w).im = c := by
      refine ⟨0, ?_⟩
      intro w hw
      by_cases hw' : w.re < 0
      · simp only [g, if_pos hw', ofReal_im]
      · simp only [g, if_neg hw', ofReal_im]
    have heq := exercise_1_13b_assumed V
      (⟨-1, hminus⟩ : V) (⟨1, hplus⟩ : V) hV hg him
    have hm : (-1 : ℂ).re < 0 := by norm_num
    have hp : ¬(1 : ℂ).re < 0 := by norm_num
    have hre := congrArg Complex.re heq
    simpa only [g, hm, hp, if_true, if_false, ofReal_re] using hre
  apply Complex.ext
  · exact h_re (f z) (f 0)
  · have hi := h_re (f z).im (f 0).im
    simpa only [ofReal_re] using hi
