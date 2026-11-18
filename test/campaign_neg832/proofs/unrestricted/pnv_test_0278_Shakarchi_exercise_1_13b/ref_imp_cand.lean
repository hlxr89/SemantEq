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
  have hleft : IsOpen {z : ℂ | z.re < 0} :=
    isOpen_lt continuous_re continuous_const
  have hright : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const continuous_re
  let Ω : Set ℂ := {z | z.re < 0} ∪ {z | 0 < z.re}
  let g : ℂ → ℂ := fun z => if z.re < 0 then 0 else 1
  have hΩ : IsOpen Ω := by
    simpa [Ω] using hleft.union hright
  have hg : DifferentiableOn ℂ g Ω := by
    intro z hz
    rcases hz with hz | hz
    · apply ((differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hleft.mem_nhds hz] with y hy
      simp [g, hy]
    · apply ((differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hright.mem_nhds hz] with y hy
      simp [g, not_lt_of_ge (le_of_lt hy)]
  have hfalse : False := by
    have heq := exercise_1_13b_assumed Ω
      (⟨(-1 : ℂ), by left; norm_num [Ω]⟩ : Ω)
      (⟨(1 : ℂ), by right; norm_num [Ω]⟩ : Ω) hΩ hg
      (by
        refine ⟨0, ?_⟩
        intro z hz
        by_cases hz0 : z.re < 0 <;> simp [g, hz0])
    simp [g] at heq
  exact hfalse.elim
