import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Set
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_5_assumed
  {f : ℝ → ℝ}
  (hfd : DifferentiableOn ℝ f (Ioi 0))
  (hf : Tendsto (deriv f) atTop (𝓝 0)) :
  Tendsto (λ x => f (x + 1) - f x) atTop (𝓝 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {f' : ℝ → E} {b : ℝ} (hf : ∀ (x : ℝ), x > b → HasDerivAt f (f' x) x) (hdf' : Tendsto f' atTop (𝓝 0)) (hb : ∀ (x : ℝ) (H : x > b), ‖f' x‖ ≤ 1) (hnb : b ≤ 0) : Tendsto (fun x => f (x + 1) - f x) atTop (𝓝 0) := by
  have hzero : Tendsto (fun x : ℝ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hzero' : Tendsto (deriv fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0) := by
    simpa using hzero
  have hscalar := exercise_5_5_assumed
    (f := fun _ : ℝ => 0) (differentiable_const (c := (0 : ℝ))).differentiableOn hzero'
  rw [Metric.tendsto_atTop] at hscalar ⊢
  intro ε hε
  obtain ⟨R, hR⟩ := hscalar (ε / 2) (by positivity)
  have hε2 : 0 < ε / 2 := by
    simpa only [sub_self, dist_zero_right, norm_zero] using hR R le_rfl
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hdf' (ε / 2) hε2
  refine ⟨max N (b + 1), fun x hx => ?_⟩
  have hbound : ∀ y ∈ Ico x (x + 1), ‖f' y‖ ≤ ε / 2 := by
    intro y hy
    exact le_of_lt (by simpa [dist_eq_norm] using hN y (le_trans (le_max_left _ _) (le_trans hx hy.1)))
  have hderiv : ∀ y ∈ Icc x (x + 1), HasDerivWithinAt f (f' y) (Icc x (x + 1)) y := by
    intro y hy
    apply (hf y ?_).hasDerivWithinAt
    linarith [le_trans (le_max_right N (b + 1)) hx, hy.1]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (x + 1)
    (right_mem_Icc.2 (by linarith : x ≤ x + 1))
  rw [show x + 1 - x = (1 : ℝ) by ring, mul_one] at hmvt
  simpa [dist_eq_norm] using lt_of_le_of_lt hmvt (by linarith)
