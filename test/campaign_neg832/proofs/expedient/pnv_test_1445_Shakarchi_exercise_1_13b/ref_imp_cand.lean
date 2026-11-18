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
  have hopen : IsOpen ({z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re}) :=
    (isOpen_lt continuous_re continuous_const).union
      (isOpen_lt continuous_const continuous_re)
  let g : ℂ → ℂ := fun z => if z.re < 0 then 0 else 1
  have hg : DifferentiableOn ℂ g ({z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re}) := by
    intro z hz
    rcases hz with hz | hz
    · apply DifferentiableAt.differentiableWithinAt
      apply (differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hz] with y hy
      simp [g, hy]
    · apply DifferentiableAt.differentiableWithinAt
      apply (differentiableAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with y hy
      simp [g, not_lt.mpr (le_of_lt hy)]
  let a : ↥({z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re}) :=
    ⟨-1, Or.inl (by norm_num)⟩
  let b : ↥({z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re}) :=
    ⟨1, Or.inr (by norm_num)⟩
  have him : ∃ c : ℝ, ∀ z ∈ ({z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re}), (g z).im = c := by
    refine ⟨0, ?_⟩
    intro z hz
    by_cases hz : z.re < 0 <;> simp [g, hz]
  have hfalse : False := by
    have h := exercise_1_13b_assumed _ a b hopen hg him
    have : (0 : ℂ) = 1 := by simpa [a, b, g] using h
    exact zero_ne_one this
  exact hfalse.elim
