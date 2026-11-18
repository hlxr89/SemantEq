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
theorem dummy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : AnalyticOn ℂ f U) (h_im_const : ∀ z : E, z ∈ U → f z = f z) : (∀ z : E, z ∈ U → f z = f 0) := by
  let Ωbad : Set ℂ := {z : ℂ | z.re < 0} ∪ {z : ℂ | 0 < z.re}
  have hopen : IsOpen Ωbad := by
    dsimp [Ωbad]
    exact (isOpen_lt Complex.continuous_re continuous_const).union
      (isOpen_lt continuous_const Complex.continuous_re)
  have hdiff : DifferentiableOn ℂ
      (fun z : ℂ => if z.re < 0 then (0 : ℂ) else (1 : ℂ)) Ωbad := by
    intro z hz
    by_cases hn : z.re < 0
    · have he : (fun w : ℂ => if w.re < 0 then 0 else 1) =ᶠ[𝓝 z]
          (fun _ : ℂ => (0 : ℂ)) := by
        filter_upwards [Complex.continuous_re.continuousAt.eventually_lt
          continuousAt_const hn] with w hw
        simp [hw]
      exact (differentiableAt_const (c := (0 : ℂ))).differentiableWithinAt.congr_of_eventuallyEq
        (he.filter_mono inf_le_left) (by simp [hn])
    · have hp : 0 < z.re := by
        rcases hz with hz | hz
        · exact False.elim (hn hz)
        · exact hz
      have he : (fun w : ℂ => if w.re < 0 then 0 else 1) =ᶠ[𝓝 z]
          (fun _ : ℂ => (1 : ℂ)) := by
        filter_upwards [continuousAt_const.eventually_lt
          Complex.continuous_re.continuousAt hp] with w hw
        simp [not_lt.mpr (le_of_lt hw)]
      exact (differentiableAt_const (c := (1 : ℂ))).differentiableWithinAt.congr_of_eventuallyEq
        (he.filter_mono inf_le_left) (by simp [hn])
  let a : Ωbad := ⟨-1, by dsimp [Ωbad]; left; norm_num⟩
  let b : Ωbad := ⟨1, by dsimp [Ωbad]; right; norm_num⟩
  have hab := exercise_1_13b_assumed
    Ωbad a b hopen hdiff
    ⟨0, by
      intro z hz
      by_cases hn : z.re < 0
      · simp [hn]
      · simp [hn]⟩
  have : False := by
    simpa [a, b] using hab
  exact this.elim
