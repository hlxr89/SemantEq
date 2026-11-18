import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) : UniformContinuousOn f (Set.Icc a b) ↔ ∀ ε > 0, ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x y⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → |x - y| < δ → |f x - f y| < ε := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  constructor
  · intro hf
    let S : ℝ → Set ℝ := fun r ↦
      {z | ∃ s t : Icc a b, |(s : ℝ) - t| ≤ max r 0 ∧ z = |f s - f t|}
    let ω : ℝ → ℝ := fun r ↦ sSup (S r)
    have hcont : Continuous (fun p : Icc a b × Icc a b ↦ |f p.1 - f p.2|) := by
      exact ((hf.continuous.comp continuous_fst).sub
        (hf.continuous.comp continuous_snd)).abs
    have hB_range : BddAbove (Set.range fun p : Icc a b × Icc a b ↦ |f p.1 - f p.2|) :=
      (isCompact_range hcont).bddAbove
    have hB : ∀ r, BddAbove (S r) := by
      intro r
      refine hB_range.mono ?_
      rintro z ⟨s, t, hst, rfl⟩
      exact ⟨(s, t), rfl⟩
    let q : Icc a b := ⟨a, le_rfl, hab⟩
    have hne : ∀ r, (S r).Nonempty := by
      intro r
      refine ⟨0, q, q, ?_, by simp⟩
      simp
    have hω_nonneg : ∀ r, 0 ≤ ω r := by
      intro r
      apply le_csSup (hB r)
      exact ⟨q, q, by simp, by simp⟩
    have hω_mono : Monotone ω := by
      intro r u hru
      apply csSup_le (hne r)
      intro z hz
      apply le_csSup (hB u)
      rcases hz with ⟨s, t, hst, rfl⟩
      exact ⟨s, t, hst.trans (max_le_max_right 0 hru), rfl⟩
    have hω_lim : Tendsto ω (𝓝 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      rcases (Metric.uniformContinuous_iff.mp hf) (ε / 2) (half_pos hε) with
        ⟨δ, hδ, hδf⟩
      filter_upwards [Metric.ball_mem_nhds 0 hδ] with r hr
      have hrabs : |r| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hr
      have hrmax : max r 0 < δ := max_lt (lt_of_le_of_lt (le_abs_self r) hrabs) hδ
      have hω_le : ω r ≤ ε / 2 := by
        apply csSup_le (hne r)
        rintro z ⟨s, t, hst, rfl⟩
        exact (hδf (by simpa [Real.dist_eq] using hst.trans_lt hrmax)).le
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hω_nonneg r)]
      exact hω_le.trans_lt (half_lt_self hε)
    refine ⟨fun r ↦ r + ω r, ?_⟩
    intro r
    constructor
    · intro hr
      exact add_pos_of_pos_of_nonneg hr (hω_nonneg r)
    constructor
    · intro x hx y hy hxy
      exact add_lt_add_of_lt_of_le hxy (hω_mono hxy.le)
    constructor
    · simpa only [Pi.add_apply, id_eq, zero_add] using
        continuousAt_id.tendsto.add hω_lim
    · intro s t
      have hmem : |f s - f t| ∈ S (|(s : ℝ) - t|) := by
        refine ⟨s, t, ?_, rfl⟩
        simp
      exact (le_csSup (hB _) hmem).trans
        (le_add_of_nonneg_left (abs_nonneg ((s : ℝ) - t)))
  · rintro ⟨μ, hμ⟩
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    have hev : ∀ᶠ x : ℝ in 𝓝 0, dist (μ x) 0 < ε :=
      (Metric.tendsto_nhds.mp (hμ 0).2.2.1) ε hε
    rcases (Metric.eventually_nhds_iff.mp hev) with ⟨δ, hδ, hball⟩
    refine ⟨δ, hδ, ?_⟩
    intro s t hst
    have habs : |(s : ℝ) - t| ∈ Metric.ball (0 : ℝ) δ := by
      simpa [Metric.mem_ball, Real.dist_eq] using hst
    have hlt : |μ (|(s : ℝ) - t|)| < ε := by
      simpa [Real.dist_eq] using hball habs
    rw [Real.dist_eq]
    exact (hμ (|(s : ℝ) - t|)).2.2.2 s t |>.trans_lt
      (lt_of_le_of_lt (le_abs_self _) hlt)
