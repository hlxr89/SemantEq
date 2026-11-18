import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Set
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {f' : ℝ → E} {b : ℝ} (hf : ∀ (x : ℝ), x > b → HasDerivAt f (f' x) x) (hdf' : Tendsto f' atTop (𝓝 0)) (hb : ∀ (x : ℝ) (H : x > b), ‖f' x‖ ≤ 1) (hnb : b ≤ 0) : Tendsto (fun x => f (x + 1) - f x) atTop (𝓝 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_5
  {f : ℝ → ℝ}
  (hfd : DifferentiableOn ℝ f (Ioi 0))
  (hf : Tendsto (deriv f) atTop (𝓝 0)) :
  Tendsto (λ x => f (x + 1) - f x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hf ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hf (ε / 2) (half_pos hε)
  refine ⟨max N 1, fun x hx => ?_⟩
  have hxN : N ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hx)
  have hderiv : ∀ y ∈ Icc x (x + 1), ‖deriv f y‖ ≤ ε / 2 := by
    intro y hy
    have hyN : N ≤ y := hxN.trans hy.1
    simpa [dist_eq_norm] using le_of_lt (hN y hyN)
  have hmv : ‖f (x + 1) - f x‖ ≤ (ε / 2) * ‖(x + 1) - x‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Icc x (x + 1)) ?_ hderiv (convex_Icc _ _) ?_ ?_
    · intro y hy
      apply hfd.differentiableAt
      exact Ioi_mem_nhds (hx0.trans_le hy.1)
    · exact left_mem_Icc.2 (by linarith)
    · exact right_mem_Icc.2 (by linarith)
  simpa [dist_eq_norm] using
    (show ‖f (x + 1) - f x‖ < ε from
      lt_of_le_of_lt (by simpa using hmv) (half_lt_self hε))
