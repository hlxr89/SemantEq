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
  have hopen : IsOpen {z : ℂ | z.re ≠ 0} := by
    exact (isClosed_eq Complex.continuous_re continuous_const).isOpen_compl
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => if z.re < 0 then (0 : ℂ) else 1) {z | z.re ≠ 0} := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    rcases lt_or_gt_of_ne hz with hz | hz
    · apply (Filter.EventuallyEq.differentiableAt_iff _).2 (differentiableAt_const (𝕜 := ℂ) 0)
      filter_upwards [Complex.continuous_re.continuousAt.eventually_lt continuousAt_const hz] with w hw
      simp [hw]
    · apply (Filter.EventuallyEq.differentiableAt_iff _).2 (differentiableAt_const (𝕜 := ℂ) 1)
      filter_upwards [continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hz] with w hw
      simp [not_lt_of_ge (le_of_lt hw)]
  have hfalse := exercise_1_13b_assumed {z : ℂ | z.re ≠ 0}
    (⟨-1, by norm_num⟩ : {z : ℂ | z.re ≠ 0})
    (⟨1, by norm_num⟩ : {z : ℂ | z.re ≠ 0}) hopen hdiff
    ⟨0, by intro z hz; split <;> simp⟩
  norm_num at hfalse

