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
  exfalso
  let Ω : Set ℂ := {z | z.re < 0} ∪ {z | 0 < z.re}
  let g : ℂ → ℂ := fun z => if z.re < 0 then 0 else 1
  have hopen : IsOpen Ω :=
    (isOpen_lt continuous_re continuous_const).union
      (isOpen_lt continuous_const continuous_re)
  have hdiff : DifferentiableOn ℂ g Ω := by
    intro z hz
    rcases hz with hz | hz
    · have he : ∀ᶠ w in 𝓝 z, w.re < 0 :=
        (isOpen_lt continuous_re continuous_const).mem_nhds hz
      exact ((differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        (he.mono fun w hw => by simp [g, hw])).differentiableWithinAt
    · have he : ∀ᶠ w in 𝓝 z, 0 < w.re :=
        (isOpen_lt continuous_const continuous_re).mem_nhds hz
      exact ((differentiableAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
        (he.mono fun w hw => by simp [g, not_lt_of_ge hw.le])).differentiableWithinAt
  have him : ∃ (c : ℝ), ∀ z ∈ Ω, (g z).im = c := by
    refine ⟨0, ?_⟩
    intro z hz
    dsimp [g]
    split <;> simp
  have bad := exercise_1_13b_assumed Ω
    (⟨(-1 : ℂ), by left; norm_num [Ω]⟩)
    (⟨(1 : ℂ), by right; norm_num [Ω]⟩) hopen hdiff him
  norm_num [g] at bad
