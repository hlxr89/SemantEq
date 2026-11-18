import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (h : ∀ x : ℝ, Tendsto (fun h : ℝ => (f (x + h) - f (x - h))) (𝓝 0) (𝓝 0)) : ∃ x, ContinuousAt f x ∧ ¬ ContinuousAt f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  let f : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  refine ⟨f, ?_, ?_⟩
  · intro x
    refine (tendsto_congr' (f₂ := fun _ => 0) ?_).2 tendsto_const_nhds
    by_cases hx : x = 0
    · subst x
      filter_upwards with y
      simp [f]
    · have hev : Metric.ball (0 : ℝ) |x| ∈ 𝓝 0 :=
        Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (abs_pos.mpr hx))
      filter_upwards [hev] with y hy
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
      have h₁ : x + y ≠ 0 := by
        intro hxy
        have : y = -x := by linarith
        rw [this, abs_neg] at hy
        exact (lt_irrefl _ hy)
      have h₂ : x - y ≠ 0 := by
        intro hxy
        have : y = x := by linarith
        rw [this] at hy
        exact (lt_irrefl _ hy)
      simp [f, h₁, h₂]
  · intro hf
    have hevent : ∀ᶠ x in 𝓝 (0 : ℝ), dist (f x) (f 0) < (1 / 2 : ℝ) :=
      (Metric.tendsto_nhds.1 hf.continuousAt) (1 / 2) (by norm_num)
    rcases Metric.mem_nhds_iff.1 hevent with ⟨ε, hε, hball⟩
    have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      simp only [sub_zero]
      rw [abs_of_pos (half_pos hε)]
      linarith
    have := hball hmem
    simp [f, ne_of_gt (half_pos hε)] at this
    norm_num at this
