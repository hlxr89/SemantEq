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
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    have hgdiff : DifferentiableOn ℂ (fun _ : ℂ ↦ f 0) Set.univ := by
      intro w hw
      exact (differentiableAt_const (x := w) (f 0)).differentiableWithinAt
    have hgim : ∃ (c : ℝ), ∀ w ∈ Set.univ, ((fun _ : ℂ ↦ f 0) w).im = c := by
      exact ⟨(f 0).im, fun w hw ↦ rfl⟩
    exact exercise_1_13b_assumed (f := fun _ : ℂ ↦ f 0) Set.univ
      ⟨0, Set.mem_univ 0⟩ ⟨0, Set.mem_univ 0⟩ isOpen_univ hgdiff hgim
  · let U : Set ℂ := {w | dist w z < dist w 0}
    let V : Set ℂ := {w | dist w 0 < dist w z}
    let A : Set ℂ := U ∪ V
    let g : ℂ → ℂ := fun w ↦ if w ∈ U then f z else f 0
    have hU : IsOpen U := by
      exact isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)
    have hV : IsOpen V := by
      exact isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)
    have hA : IsOpen A := hU.union hV
    have hzU : z ∈ U := by
      change dist z z < dist z 0
      rw [dist_self]
      exact dist_pos.mpr hz0
    have h0V : (0 : ℂ) ∈ V := by
      change dist 0 0 < dist 0 z
      rw [dist_self]
      exact dist_pos.mpr (Ne.symm hz0)
    have hgdiff : DifferentiableOn ℂ g A := by
      intro w hw
      rcases hw with hw | hw
      · have heq : g =ᶠ[nhdsWithin w A] (fun _ ↦ f z) := by
          filter_upwards [Filter.Eventually.filter_mono inf_le_left (hU.mem_nhds hw)] with y hy
          have hyU : y ∈ U := hy
          change (if y ∈ U then f z else f 0) = f z
          rw [if_pos hyU]
        exact (differentiableAt_const (x := w) (f z)).differentiableWithinAt.congr_of_eventuallyEq
          heq (if_pos hw)
      · have heq : g =ᶠ[nhdsWithin w A] (fun _ ↦ f 0) := by
          filter_upwards [Filter.Eventually.filter_mono inf_le_left (hV.mem_nhds hw)] with y hy
          have hynU : y ∉ U := by
            intro hyU
            change dist y z < dist y 0 at hyU
            exact (not_lt_of_ge (le_of_lt hy)) hyU
          change (if y ∈ U then f z else f 0) = f 0
          rw [if_neg hynU]
        have hwnU : w ∉ U := by
          intro hwU
          change dist w z < dist w 0 at hwU
          exact (not_lt_of_ge (le_of_lt hw)) hwU
        exact (differentiableAt_const (x := w) (f 0)).differentiableWithinAt.congr_of_eventuallyEq
          heq (if_neg hwnU)
    have hgim : ∃ (c : ℝ), ∀ w ∈ A, (g w).im = c := by
      refine ⟨(f z).im, ?_⟩
      intro w hw
      by_cases hwU : w ∈ U
      · change (if w ∈ U then f z else f 0).im = (f z).im
        rw [if_pos hwU]
      · change (if w ∈ U then f z else f 0).im = (f z).im
        rw [if_neg hwU, hc z hz]
    have hzg := exercise_1_13b_assumed A ⟨z, Or.inl hzU⟩ ⟨0, Or.inr h0V⟩ hA hgdiff hgim
    change (if z ∈ U then f z else f 0) = (if (0 : ℂ) ∈ U then f z else f 0) at hzg
    have h0nU : (0 : ℂ) ∉ U := by
      intro h0U
      change dist 0 z < dist 0 0 at h0U
      exact (not_lt_of_ge (le_of_lt h0V)) h0U
    rw [if_pos hzU, if_neg h0nU] at hzg
    exact hzg
