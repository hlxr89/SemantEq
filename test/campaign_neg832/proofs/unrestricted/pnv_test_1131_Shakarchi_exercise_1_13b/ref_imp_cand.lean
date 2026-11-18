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
theorem dummy {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOn ℂ f U) (h : ∀ x ∈ U, (f x).im = 0) : ∀ x ∈ U, f x = x := by
  have hopen : IsOpen ({z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re}) :=
    (isOpen_lt continuous_re continuous_const).union
      (isOpen_lt continuous_const continuous_re)
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => if z.re < 0 then (0 : ℂ) else 1)
      ({z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re}) := by
    intro z hz
    rcases hz with hz | hz
    · have he : (fun y : ℂ => if y.re < 0 then (0 : ℂ) else 1) =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hz] with y hy
        simp [hy]
      exact (he.differentiableAt_iff.mpr (by fun_prop)).differentiableWithinAt
    · have he : (fun y : ℂ => if y.re < 0 then (0 : ℂ) else 1) =ᶠ[𝓝 z] fun _ => 1 := by
        filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with y hy
        simp [not_lt.mpr (le_of_lt hy)]
      exact (he.differentiableAt_iff.mpr (by fun_prop)).differentiableWithinAt
  let a : ({z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re} : Set ℂ) :=
    ⟨-1, Or.inl (by norm_num)⟩
  let b : ({z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re} : Set ℂ) :=
    ⟨1, Or.inr (by norm_num)⟩
  have hab := exercise_1_13b_assumed
    ({z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re}) a b hopen hdiff
    ⟨0, by intro z hz; split <;> simp⟩
  norm_num [a, b] at hab

