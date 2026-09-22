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
theorem dummy {Ω : Set ℂ} (h : IsOpen Ω) {f : ℂ → ℂ} (hf : AnalyticOn ℂ f Ω) (hc : ∀ z ∈ Ω, (f z).im = (f 0).im) : (∀ z ∈ Ω, f z = f 0) := by
  exfalso
  let U : Set ℂ := {z | z.re < 0} ∪ {z | 0 < z.re}
  let g : ℂ → ℂ := fun z => if z.re < 0 then 0 else 1
  have hU : IsOpen U := by
    exact (isOpen_lt continuous_re continuous_const).union
      (isOpen_lt continuous_const continuous_re)
  have hg : DifferentiableOn ℂ g U := by
    intro z hz
    rcases hz with hz | hz
    · have hn : ∀ᶠ w in 𝓝 z, w.re < 0 :=
        (isOpen_lt continuous_re continuous_const).mem_nhds hz
      have heq : g =ᶠ[𝓝 z] (fun _ : ℂ => 0) := by
        filter_upwards [hn] with w hw
        simp [g, hw]
      exact (differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq heq |>.differentiableWithinAt
    · have hp : ∀ᶠ w in 𝓝 z, 0 < w.re :=
        (isOpen_lt continuous_const continuous_re).mem_nhds hz
      have heq : g =ᶠ[𝓝 z] (fun _ : ℂ => 1) := by
        filter_upwards [hp] with w hw
        simp [g, not_lt.mpr (le_of_lt hw)]
      exact (differentiableAt_const (c := (1 : ℂ))).congr_of_eventuallyEq heq |>.differentiableWithinAt
  let a : U := ⟨-1, by left; norm_num⟩
  let b : U := ⟨1, by right; norm_num⟩
  have him : ∃ c : ℝ, ∀ z ∈ U, (g z).im = c := by
    refine ⟨0, ?_⟩
    intro z hz
    simp only [g]
    split <;> simp
  have hab := exercise_1_13b_assumed U a b hU hg him
  norm_num [g, a, b] at hab
