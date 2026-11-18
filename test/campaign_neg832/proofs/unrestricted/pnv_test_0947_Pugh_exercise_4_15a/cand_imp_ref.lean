import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), (∀ (ε : ℝ), ε > 0 → μ ε > 0) ∧ (∀ (ε : ℝ), ε > 0 → ∀ (x y : X), dist x y < μ ε → dist (f x) (f y) < ε) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  constructor
  · intro hf
    let S : ℝ → Set ℝ := fun x =>
      {z | ∃ s t : Icc a b, dist s t ≤ max x 0 ∧ z = dist (f s) (f t)}
    let w : ℝ → ℝ := fun x => sSup (S x)
    have hS_ne : ∀ x, (S x).Nonempty := by
      intro x
      let s : Icc a b := ⟨a, mem_Icc.2 ⟨le_rfl, hab⟩⟩
      refine ⟨0, s, s, ?_, by simp⟩
      simp
    have hS_bdd : ∀ x, BddAbove (S x) := by
      have hrange : BddAbove (range fun s : Icc a b => |f s|) :=
        (isCompact_range (continuous_abs.comp hf.continuous)).bddAbove
      obtain ⟨C, hC⟩ := hrange
      intro x
      refine ⟨C + C, ?_⟩
      rintro z ⟨s, t, hst, rfl⟩
      rw [Real.dist_eq]
      exact (abs_sub (f s) (f t)).trans
        (add_le_add (hC (mem_range_self s)) (hC (mem_range_self t)))
    have hw_nonneg : ∀ x, 0 ≤ w x := by
      intro x
      apply le_csSup (hS_bdd x)
      let s : Icc a b := ⟨a, mem_Icc.2 ⟨le_rfl, hab⟩⟩
      exact ⟨s, s, by simp, by simp⟩
    have hw_mono : Monotone w := by
      intro x y hxy
      apply csSup_le_csSup (hS_bdd y) (hS_ne x)
      rintro z ⟨s, t, hst, rfl⟩
      exact ⟨s, t, hst.trans (max_le_max hxy le_rfl), rfl⟩
    have hw_lim : Tendsto w (𝓝 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hcontrol⟩ :=
        (Metric.uniformContinuous_iff.mp hf) (ε / 2) (by linarith)
      refine ⟨min δ ε, lt_min hδ hε, ?_⟩
      intro x hx
      have hxδ : max x 0 < δ := by
        rw [Real.dist_eq, sub_zero] at hx
        have : |x| < δ := hx.trans_le (min_le_left _ _)
        exact max_lt (lt_of_le_of_lt (le_abs_self x) this) hδ
      have hwε : w x ≤ ε / 2 := by
        apply csSup_le (hS_ne x)
        rintro z ⟨s, t, hst, rfl⟩
        exact (hcontrol (hst.trans_lt hxδ)).le
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hw_nonneg x)]
      linarith
    refine ⟨fun x => x + w x, ?_⟩
    intro x
    constructor
    · intro hx
      have := hw_nonneg x
      linarith
    constructor
    · intro u hu v hv huv
      have hwy := hw_mono huv.le
      linarith
    constructor
    · simpa using tendsto_id.add hw_lim
    · intro s t
      have hdist_nonneg : 0 ≤ dist s t := dist_nonneg
      have hmem : dist (f s) (f t) ∈ S (dist s t) := by
        exact ⟨s, t, by simp [hdist_nonneg], rfl⟩
      have hle : dist (f s) (f t) ≤ w (dist s t) :=
        le_csSup (hS_bdd _) hmem
      simp only [Real.dist_eq] at hle ⊢
      exact hle.trans (le_add_of_nonneg_left (abs_nonneg ((s : ℝ) - (t : ℝ))))
  · rintro ⟨μ, hμ⟩
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    have hevent : ∀ᶠ x in 𝓝 (0 : ℝ), dist (μ x) 0 < ε :=
      (Metric.tendsto_nhds.mp (hμ 1).2.2.1) ε hε
    have hnear : {x : ℝ | dist x 0 < 1} ∩ {x : ℝ | dist (μ x) 0 < ε} ∈ 𝓝 0 :=
      inter_mem (Metric.ball_mem_nhds 0 zero_lt_one) hevent
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
    refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
    intro s t hst
    have hd_mem : dist s t ∈ {x : ℝ | dist x 0 < 1} ∩ {x : ℝ | dist (μ x) 0 < ε} := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
      exact hst.trans_le (min_le_left _ _)
    have hbound := (hμ (dist s t)).2.2.2 s t
    have hμlt : μ (dist s t) < ε := by
      have := hd_mem.2
      change dist (μ (dist s t)) 0 < ε at this
      rw [Real.dist_eq, sub_zero] at this
      exact lt_of_le_of_lt (le_abs_self _) this
    simpa only [Real.dist_eq] using hbound.trans_lt hμlt
