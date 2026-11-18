import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) (hf : ∀ x, Tendsto (fun h => f (x + h) - f (x - h)) (𝓝[>] 0) (𝓝 0)) : ∃ x, ¬Tendsto (deriv f) (𝓝 x) (𝓝 (deriv f x)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  refine ⟨fun x : ℝ => if x = 0 then 1 else 0, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst x
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
    · have hplus : ∀ᶠ y : ℝ in 𝓝 0, x + y ≠ 0 := by
        have ht : Tendsto (fun y : ℝ => x + y) (𝓝 0) (𝓝 x) := by
          have hc : ContinuousAt (fun y : ℝ => x + y) 0 := by fun_prop
          simpa only [ContinuousAt, add_zero] using hc
        exact ht (isOpen_compl_singleton.eventually_mem hx)
      have hminus : ∀ᶠ y : ℝ in 𝓝 0, x - y ≠ 0 := by
        have ht : Tendsto (fun y : ℝ => x - y) (𝓝 0) (𝓝 x) := by
          have hc : ContinuousAt (fun y : ℝ => x - y) 0 := by fun_prop
          simpa only [ContinuousAt, sub_zero] using hc
        exact ht (isOpen_compl_singleton.eventually_mem hx)
      apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hplus, hminus] with y hyplus hyminus
      simp [hyplus, hyminus]
  · intro hcont
    have hc0 := hcont.continuousAt (x := (0 : ℝ))
    rw [Metric.continuousAt_iff] at hc0
    obtain ⟨δ, hδ, hbound⟩ := hc0 (1 / 2) (by norm_num)
    have hy0 : δ / 2 ≠ (0 : ℝ) := by positivity
    have hydist : dist (δ / 2) (0 : ℝ) < δ := by
      rw [Real.dist_eq]
      rw [abs_of_nonneg (by linarith)]
      linarith
    have := hbound hydist
    norm_num [hy0] at this
