import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) : UniformContinuousOn f (Set.Icc a b) ↔ ∃ (M : ℝ → ℝ), ContinuousOn f (Set.Icc a b) ∧ (∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ ⦃x y⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → abs (x - y) < ε → abs (f x - f y) ≤ M ε) ∧ Tendsto M (𝓝[>] 0) (𝓝 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  constructor
  · intro hf
    let S : ℝ → Set ℝ := fun x => {0} ∪ {z | ∃ s t : Icc a b,
      dist s t ≤ x ∧ z = dist (f s) (f t)}
    let μ : ℝ → ℝ := fun x => x + sSup (S x)
    have hcont : Continuous f := hf.continuous
    have hbdd : ∃ C : ℝ, ∀ s t : Icc a b, dist (f s) (f t) ≤ C := by
      exact Metric.isBounded_range_iff.mp (isCompact_range hcont).isBounded
    obtain ⟨C, hC⟩ := hbdd
    have hS_nonempty (x : ℝ) : (S x).Nonempty := by
      exact ⟨0, Or.inl rfl⟩
    have hS_bdd (x : ℝ) : BddAbove (S x) := by
      refine ⟨max 0 C, fun z hz => ?_⟩
      rcases hz with (rfl | ⟨s, t, _, rfl⟩)
      · exact le_max_left _ _
      · exact (hC s t).trans (le_max_right _ _)
    have hosc_nonneg (x : ℝ) : 0 ≤ sSup (S x) :=
      le_csSup (hS_bdd x) (Or.inl rfl)
    have hosc_mono : Monotone fun x => sSup (S x) := by
      intro x y hxy
      apply csSup_le (hS_nonempty x)
      intro z hz
      apply le_csSup (hS_bdd y)
      rcases hz with (rfl | ⟨s, t, hst, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨s, t, hst.trans hxy, rfl⟩
    have hosc_lim : Tendsto (fun x => sSup (S x)) (𝓝 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, huc⟩ := (Metric.uniformContinuous_iff_le.mp hf) (ε / 2) (half_pos hε)
      filter_upwards [Metric.ball_mem_nhds 0 (lt_min hδ (half_pos hε))] with x hx
      have hx' : |x| < min δ (ε / 2) := by
        simpa [Metric.mem_ball, Real.dist_eq] using hx
      have hxδ : x ≤ δ := by
        have : x < δ := lt_of_le_of_lt (le_abs_self x) (lt_of_lt_of_le hx' (min_le_left _ _))
        simpa [Real.dist_eq] using this.le
      have hsup : sSup (S x) ≤ ε / 2 := by
        apply csSup_le (hS_nonempty x)
        intro z hz
        rcases hz with (rfl | ⟨s, t, hst, rfl⟩)
        · exact (half_pos hε).le
        · exact huc (hst.trans hxδ)
      rw [Real.dist_eq, sub_zero]
      rw [abs_of_nonneg (hosc_nonneg x)]
      exact hsup.trans_lt (half_lt_self hε)
    refine ⟨μ, fun x => ?_⟩
    refine ⟨fun hx => add_pos_of_pos_of_nonneg hx (hosc_nonneg x), ?_, ?_, ?_⟩
    · intro u hu v hv huv
      exact add_lt_add_of_lt_of_le huv (hosc_mono huv.le)
    · simpa [μ] using tendsto_id.add hosc_lim
    · intro s t
      have hmem : dist (f s) (f t) ∈ S (dist s t) :=
        Or.inr ⟨s, t, le_rfl, rfl⟩
      have hs : dist (f s) (f t) ≤ sSup (S (dist s t)) :=
        le_csSup (hS_bdd _) hmem
      have := hs.trans (le_add_of_nonneg_left (dist_nonneg : 0 ≤ dist s t))
      simpa [μ, Real.dist_eq, Subtype.dist_eq] using this
  · rintro ⟨μ, hμ⟩
    exact (Metric.uniformEquicontinuous_of_continuity_modulus μ (hμ 0).2.2.1
      (fun _ : Unit => f) (fun x y _ => by
        simpa [Real.dist_eq, Subtype.dist_eq] using (hμ 0).2.2.2 x y)).uniformContinuous ()
