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
    let g : (Icc a b × Icc a b) → ℝ := fun p => |f p.1 - f p.2|
    have hg : Continuous g := by
      have hf' : Continuous f := hf.continuous
      fun_prop
    have hB : BddAbove (range g) := (isCompact_range hg).bddAbove
    let ω : ℝ → ℝ := fun r => sSup {z | ∃ s t : Icc a b,
      |(s : ℝ) - t| ≤ max r 0 ∧ z = |f s - f t|}
    have hsetB : ∀ r : ℝ, BddAbove {z | ∃ s t : Icc a b,
        |(s : ℝ) - t| ≤ max r 0 ∧ z = |f s - f t|} := by
      intro r
      apply hB.mono
      rintro z ⟨s, t, hst, rfl⟩
      exact ⟨(s, t), rfl⟩
    have hzero : ∀ r : ℝ, 0 ∈ {z | ∃ s t : Icc a b,
        |(s : ℝ) - t| ≤ max r 0 ∧ z = |f s - f t|} := by
      intro r
      let s : Icc a b := ⟨a, left_mem_Icc.2 hab⟩
      exact ⟨s, s, by simp, by simp⟩
    have hω_nonneg : ∀ r, 0 ≤ ω r := by
      intro r
      exact le_csSup (hsetB r) (hzero r)
    have hω_le (r : ℝ) (s t : Icc a b) (hst : |(s : ℝ) - t| ≤ max r 0) :
        |f s - f t| ≤ ω r := by
      exact le_csSup (hsetB r) ⟨s, t, hst, rfl⟩
    have hω_mono : Monotone ω := by
      intro r q hrq
      apply csSup_le (α := ℝ) ⟨0, hzero r⟩
      rintro z ⟨s, t, hst, rfl⟩
      apply hω_le q s t
      exact hst.trans (max_le_max_right 0 hrq)
    have hω_lim : Tendsto ω (𝓝 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuous_iff_le.mp hf) (ε / 2) (by positivity)
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with r hr
      change dist r 0 < δ at hr
      rw [Real.dist_eq, sub_zero] at hr
      have hmax : max r 0 ≤ δ := by
        rw [max_le_iff]
        exact ⟨(le_abs_self r).trans hr.le, hδ.le⟩
      have hupper : ω r ≤ ε / 2 := by
        apply csSup_le (α := ℝ) ⟨0, hzero r⟩
        rintro z ⟨s, t, hst, rfl⟩
        simpa only [Real.dist_eq] using hmod (hst.trans hmax)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hω_nonneg r)]
      exact hupper.trans_lt (half_lt_self hε)
    refine ⟨fun r => r + ω r, fun x => ?_⟩
    constructor
    · intro hx
      exact add_pos_of_pos_of_nonneg hx (hω_nonneg x)
    constructor
    · intro x hx y hy hxy
      exact add_lt_add_of_lt_of_le hxy (hω_mono hxy.le)
    constructor
    · simpa using tendsto_id.add hω_lim
    · intro s t
      have hdist : |(s : ℝ) - t| ≤ max |(s : ℝ) - t| 0 := le_max_left _ _
      exact (hω_le _ s t hdist).trans (le_add_of_nonneg_left (abs_nonneg _))
  · rintro ⟨μ, hμ⟩
    rw [Metric.uniformContinuous_iff_le]
    intro ε hε
    have hm : {x | μ x < ε} ∈ 𝓝 (0 : ℝ) :=
      (hμ 0).2.2.1 (Iio_mem_nhds hε)
    rcases Metric.mem_nhds_iff.mp hm with ⟨δ, hδ, hball⟩
    refine ⟨δ / 2, by positivity, fun s t hst => ?_⟩
    have hd : dist (dist s t) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
      exact hst.trans_lt (half_lt_self hδ)
    have hμlt : μ (dist s t) < ε := hball hd
    have hbound := (hμ (dist s t)).2.2.2 s t
    simpa only [Real.dist_eq] using hbound.trans hμlt.le
