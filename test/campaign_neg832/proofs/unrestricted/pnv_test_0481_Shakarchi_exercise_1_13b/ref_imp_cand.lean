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
  let Ω : Set ℂ := {z | z.re ≠ 0}
  let g : ℂ → ℂ := fun z => if z.re < 0 then 0 else 1
  have hΩ : IsOpen Ω := by
    simpa [Ω] using isOpen_ne_fun continuous_re
      (continuous_const : Continuous (fun _ : ℂ => (0 : ℝ)))
  have hg : DifferentiableOn ℂ g Ω := by
    intro z hz
    simp only [Ω, Set.mem_setOf_eq] at hz
    rcases lt_or_gt_of_ne hz with hzneg | hzpos
    · have hev : ∀ᶠ w in 𝓝 z, w.re < 0 :=
        (isOpen_lt continuous_re continuous_const).mem_nhds hzneg
      have heq : g =ᶠ[𝓝 z] (fun _ : ℂ => 0) := by
        filter_upwards [hev] with w hw
        simp [g, hw]
      exact (heq.differentiableAt_iff.mpr (differentiableAt_const 0)).differentiableWithinAt
    · have hevpos : ∀ᶠ w in 𝓝 z, 0 < w.re :=
        (isOpen_lt continuous_const continuous_re).mem_nhds hzpos
      have hev : ∀ᶠ w in 𝓝 z, ¬w.re < 0 :=
        hevpos.mono (fun w hw hlt => (not_lt_of_ge (le_of_lt hw)) hlt)
      have heq : g =ᶠ[𝓝 z] (fun _ : ℂ => 1) := by
        filter_upwards [hev] with w hw
        simp [g, hw]
      exact (heq.differentiableAt_iff.mpr (differentiableAt_const 1)).differentiableWithinAt
  have hgi : ∃ (c : ℝ), ∀ z ∈ Ω, (g z).im = c := by
    refine ⟨0, ?_⟩
    intro z hz
    simp only [g]
    split <;> norm_num
  let a : Ω := ⟨-1, by simp [Ω]⟩
  let b : Ω := ⟨1, by simp [Ω]⟩
  have bad := exercise_1_13b_assumed Ω a b hΩ hg hgi
  have : (0 : ℂ) = 1 := by simpa [g, a, b] using bad
  norm_num at this
