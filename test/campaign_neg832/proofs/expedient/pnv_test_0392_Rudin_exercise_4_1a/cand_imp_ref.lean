import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) (hf : ∀ (x : ℝ), ∃ (h : ℝ), ∀ (h0 : 0 < h), |f (x + h) - f x| < h) (h : ¬ UniformContinuous f) : ∃ x : ℝ, ContinuousAt f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  let f : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  refine ⟨f, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst x
      simp [f]
    · have hp : Tendsto (fun y : ℝ => x + y) (𝓝 0) (𝓝 x) := by
        simpa using (tendsto_const_nhds.add
          (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝 0) (𝓝 0)))
      have hm : Tendsto (fun y : ℝ => x - y) (𝓝 0) (𝓝 x) := by
        simpa using (tendsto_const_nhds.sub
          (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝 0) (𝓝 0)))
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hp.eventually (eventually_ne_nhds hx),
        hm.eventually (eventually_ne_nhds hx)] with y hy₁ hy₂
      simp [f, hy₁, hy₂]
  · intro hc
    have hc0 : ContinuousAt f 0 := hc.continuousAt
    have h₁ : Tendsto f (𝓝[≠] 0) (𝓝 1) := by
      simpa [f] using hc0.mono_left inf_le_left
    have h₀ : Tendsto f (𝓝[≠] 0) (𝓝 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
      simp [f, hx]
    letI : NeBot (𝓝[≠] (0 : ℝ)) := inferInstance
    have : (1 : ℝ) = 0 := tendsto_nhds_unique h₁ h₀
    norm_num at this
