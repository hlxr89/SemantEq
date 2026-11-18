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
theorem dummy {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hf_diff : DifferentiableOn ℂ f s) (hf_im : ∀ z, z ∈ s → f z = f z) : ∀ z w, z ∈ s → w ∈ s → f z = f w := by
  intro z w hz hw
  have coord_eq (x y : ℝ) : x = y := by
    let Ω : Set ℂ := {q | q.re < 0} ∪ {q | 0 < q.re}
    let g : ℂ → ℂ := fun q => if q.re < 0 then (x : ℂ) else (y : ℂ)
    have hΩ : IsOpen Ω :=
      (isOpen_lt continuous_re continuous_const).union
        (isOpen_lt continuous_const continuous_re)
    have hg : DifferentiableOn ℂ g Ω := by
      intro q hq
      rcases hq with hq | hq
      · change q.re < 0 at hq
        have hevent : ∀ᶠ r in 𝓝 q, r.re < 0 :=
          (isOpen_lt continuous_re continuous_const).mem_nhds hq
        have heq : g =ᶠ[𝓝 q] fun _ => (x : ℂ) := by
          filter_upwards [hevent] with r hr
          simp [g, hr]
        exact (differentiableAt_const (𝕜 := ℂ) (x : ℂ)).differentiableWithinAt.congr_of_eventuallyEq
          (heq.filter_mono inf_le_left) (by simp [g, hq])
      · change 0 < q.re at hq
        have hevent : ∀ᶠ r in 𝓝 q, 0 < r.re :=
          (isOpen_lt continuous_const continuous_re).mem_nhds hq
        have heq : g =ᶠ[𝓝 q] fun _ => (y : ℂ) := by
          filter_upwards [hevent] with r hr
          simp [g, not_lt.mpr (le_of_lt hr)]
        exact (differentiableAt_const (𝕜 := ℂ) (y : ℂ)).differentiableWithinAt.congr_of_eventuallyEq
          (heq.filter_mono inf_le_left) (by simp [g, not_lt.mpr (le_of_lt hq)])
    let a : Ω := ⟨(-1 : ℂ), by left; norm_num [Ω]⟩
    let b : Ω := ⟨(1 : ℂ), by right; norm_num [Ω]⟩
    have hxy := exercise_1_13b_assumed Ω a b hΩ hg ⟨0, by
      intro q hq
      dsimp [g]
      split <;> simp⟩
    norm_num [g, a, b] at hxy
    exact_mod_cast hxy
  apply Complex.ext
  · exact coord_eq (f z).re (f w).re
  · exact coord_eq (f z).im (f w).im
