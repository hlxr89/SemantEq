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
  intro _
  exfalso
  let Ω : Set ℂ := {z | z.re ≠ 0}
  let g : ℂ → ℂ := fun z => if z.re < 0 then 0 else 1
  have hΩ : IsOpen Ω := by
    exact (isClosed_singleton.preimage continuous_re).isOpen_compl
  have hg : DifferentiableOn ℂ g Ω := by
    intro z hz
    change z.re ≠ 0 at hz
    by_cases hn : z.re < 0
    · have hevent : ∀ᶠ w in 𝓝 z, w.re < 0 :=
        (isOpen_lt continuous_re continuous_const).mem_nhds hn
      apply DifferentiableAt.differentiableWithinAt
      apply (differentiableAt_const (x := z) (0 : ℂ)).congr_of_eventuallyEq
      filter_upwards [hevent] with w hw
      simp [g, hw, hn]
    · have hp : 0 < z.re := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      have hevent : ∀ᶠ w in 𝓝 z, 0 < w.re :=
        (isOpen_lt continuous_const continuous_re).mem_nhds hp
      apply DifferentiableAt.differentiableWithinAt
      apply (differentiableAt_const (x := z) (1 : ℂ)).congr_of_eventuallyEq
      filter_upwards [hevent] with w hw
      simp [g, hn, not_lt_of_ge (le_of_lt hw)]
  have hc : ∃ (c : ℝ), ∀ z ∈ Ω, (g z).im = c := by
    refine ⟨0, ?_⟩
    intro z hz
    simp only [g]
    split <;> simp
  let a : Ω := ⟨-1, by simp [Ω]⟩
  let b : Ω := ⟨1, by simp [Ω]⟩
  have hab := exercise_1_13b_assumed Ω a b hΩ hg hc
  norm_num [g, a, b] at hab
