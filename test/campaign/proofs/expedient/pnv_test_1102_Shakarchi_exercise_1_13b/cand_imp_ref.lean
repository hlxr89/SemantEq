import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {Ω : Set ℂ} (h : IsOpen Ω) {f : ℂ → ℂ} (hf : AnalyticOn ℂ f Ω) (hc : ∀ z ∈ Ω, (f z).im = (f 0).im) : (∀ z ∈ Ω, f z = f 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_13b {f : ℂ → ℂ} (Ω : Set ℂ) (a b : Ω) (h : IsOpen Ω)
  (hf : DifferentiableOn ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).im = c) :
  f a = f b := by
  let U : Set ℂ := {z | z.re < 0} ∪ {z | 0 < z.re}
  let g : ℂ → ℂ := fun z => if z.re < 0 then 0 else 1
  have hU : IsOpen U :=
    (isOpen_lt Complex.continuous_re continuous_const).union
      (isOpen_lt continuous_const Complex.continuous_re)
  have hg : DifferentiableOn ℂ g U := by
    intro z hz
    rcases hz with hz | hz
    · change z.re < 0 at hz
      apply DifferentiableAt.differentiableWithinAt
      apply (differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).eventually_mem hz] with w hw
      simp [g, hw]
    · change 0 < z.re at hz
      apply DifferentiableAt.differentiableWithinAt
      apply (differentiableAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem hz] with w hw
      simp [g, not_lt_of_ge (le_of_lt hw)]
  have bad := dummy_assumed hU (hg.analyticOn hU)
    (fun z hz => by by_cases hz' : z.re < 0 <;> simp [g, hz'])
    (⟨-1, by left; norm_num⟩ : U) (by left; norm_num)
  simp [g] at bad
