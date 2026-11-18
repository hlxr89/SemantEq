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
  have hbigO : (fun _ : ℝ => (1 : ℝ)) =O[atTop] (fun x => x) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp [abs_of_nonneg (le_trans zero_le_one hx), hx]
  have hrhs : ∃ μ : ℝ → ℝ, μ =O[atTop] (fun x => x) ∧
      ∀ s t : ℝ, (-1 : ℝ) ≤ s → s ≤ t → t ≤ 1 → |g t - g s| ≤ μ (|t - s|) := by
    refine ⟨fun _ => 1, hbigO, ?_⟩
    intro s t hs hst ht
    simp only [g]
    split_ifs <;> norm_num
  have huc : UniformContinuousOn g (Set.Icc (-1 : ℝ) 1) :=
    (dummy_assumed (a := (-1 : ℝ)) (b := 1) (by norm_num) g).mpr hrhs
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) (1 / 2 : ℝ) (by norm_num)
  let y : ℝ := min (δ / 2) (1 / 2)
  have hypos : 0 < y := by
    dsimp [y]
    exact lt_min (half_pos hδ) (by norm_num)
  have hyδ : y < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hyone : y ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hc := hclose 0 (by constructor <;> norm_num) y
    (by exact ⟨by linarith, hyone⟩) (by simpa [Real.dist_eq, abs_of_pos hypos] using hyδ)
  simp [g, ne_of_gt hypos] at hc
  norm_num at hc
