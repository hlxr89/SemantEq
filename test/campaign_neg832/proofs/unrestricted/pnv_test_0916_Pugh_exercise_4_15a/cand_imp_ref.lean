import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) : (UniformContinuousOn f (Set.Icc a b)) ↔ ∃ μ : ℝ → ℝ, μ =O[atTop] (fun x => x) ∧ ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b → |f t - f s| ≤ μ (|t - s|) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  exfalso
  let g : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  have hg_rhs : ∃ μ : ℝ → ℝ, μ =O[atTop] (fun x => x) ∧
      ∀ s t : ℝ, (-1 : ℝ) ≤ s → s ≤ t → t ≤ 1 → |g t - g s| ≤ μ (|t - s|) := by
    refine ⟨fun _ => 1, ?_, ?_⟩
    · apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      simpa [abs_of_nonneg (le_trans (by norm_num) hx)] using hx
    · intro s t hs hst ht
      dsimp [g]
      split_ifs <;> norm_num
  have hg_uc : UniformContinuousOn g (Set.Icc (-1 : ℝ) 1) :=
    (dummy_assumed (a := (-1 : ℝ)) (b := 1) (by norm_num) g).2 hg_rhs
  rw [Metric.uniformContinuousOn_iff] at hg_uc
  obtain ⟨δ, hδ, hcontrol⟩ := hg_uc (1 / 2 : ℝ) (by norm_num)
  let y : ℝ := min (δ / 2) (1 / 2)
  have hy_pos : 0 < y := by
    dsimp [y]
    exact lt_min (by linarith) (by norm_num)
  have hy_lt_delta : y < δ := by
    calc
      y ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  have hy_mem : y ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · linarith
    · calc y ≤ 1 / 2 := min_le_right _ _
           _ ≤ 1 := by norm_num
  have hbad := hcontrol 0 (by norm_num) y hy_mem
  have hdist : dist (0 : ℝ) y < δ := by
    simpa [Real.dist_eq, abs_of_pos hy_pos] using hy_lt_delta
  specialize hbad hdist
  simp [g, ne_of_gt hy_pos] at hbad
  norm_num at hbad
