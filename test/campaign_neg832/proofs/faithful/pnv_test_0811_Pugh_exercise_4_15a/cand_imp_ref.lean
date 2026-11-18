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
  let F : ℝ → ℝ := fun x => if hx : x ∈ Icc a b then f ⟨x, hx⟩ else f ⟨a, le_rfl, hab⟩
  have hF (x : ℝ) (hx : x ∈ Icc a b) : F x = f ⟨x, hx⟩ := by
    rw [show F x = if hx : x ∈ Icc a b then f ⟨x, hx⟩ else f ⟨a, le_rfl, hab⟩ by rfl,
      dif_pos hx]
  constructor
  · intro huf
    have hcontF : ContinuousOn F (Icc a b) := by
      rw [continuousOn_iff_continuous_restrict]
      convert huf.continuous using 1
      funext x
      exact hF x x.property
    have hufF : UniformContinuousOn F (Icc a b) := by
      rw [uniformContinuousOn_iff_restrict]
      convert huf using 1
      funext x
      exact hF x x.property
    have heps := (dummy_assumed hcontF).mp hufF
    let S : ℝ → Set ℝ := fun x => {z | ∃ s t : Icc a b, |(s : ℝ) - t| ≤ x ∧ z = |f s - f t|}
    let ω : ℝ → ℝ := fun x => sSup (S x)
    have hbounded : ∀ x, BddAbove (S x) := by
      intro x
      have hc : Continuous (fun p : (Icc a b) × (Icc a b) => |f p.1 - f p.2|) :=
        (huf.continuous.comp continuous_fst).sub (huf.continuous.comp continuous_snd) |>.abs
      have hrange : BddAbove (Set.range fun p : (Icc a b) × (Icc a b) => |f p.1 - f p.2|) := by
        rw [show Set.range (fun p : (Icc a b) × (Icc a b) => |f p.1 - f p.2|) =
          (fun p : (Icc a b) × (Icc a b) => |f p.1 - f p.2|) '' univ by ext; simp]
        exact (isCompact_univ.image hc).bddAbove
      apply hrange.mono
      rintro z ⟨s, t, -, rfl⟩
      exact ⟨(s, t), rfl⟩
    have hω_nonneg (x : ℝ) : 0 ≤ ω x := by
      by_cases hx : 0 ≤ x
      · apply le_csSup (hbounded x)
        exact ⟨⟨a, le_rfl, hab⟩, ⟨a, le_rfl, hab⟩, by simpa, by simp⟩
      · have hempty : S x = ∅ := by
          ext z
          simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨s, t, hst, -⟩
          exact (not_le_of_gt (lt_of_not_ge hx)) ((abs_nonneg _).trans hst)
        simp [ω, hempty]
    have hω_mono : Monotone ω := by
      intro x y hxy
      by_cases hS : (S x).Nonempty
      · apply csSup_le hS
        intro z hz
        apply le_csSup (hbounded y)
        rcases hz with ⟨s, t, hst, rfl⟩
        exact ⟨s, t, hst.trans hxy, rfl⟩
      · change sSup (S x) ≤ ω y
        rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sSup_empty]
        exact hω_nonneg y
    have hω_zero : Tendsto ω (𝓝 0) (𝓝 0) := by
      rw [Metric.tendsto_nhds_nhds]
      intro ε hε
      rcases heps (ε / 2) (half_pos hε) with ⟨δ, hδ, hcontrol⟩
      refine ⟨δ, hδ, ?_⟩
      intro x hx
      rw [Real.dist_eq, sub_zero, abs_lt]
      constructor
      · exact lt_of_lt_of_le (neg_lt_zero.mpr hε) (hω_nonneg x)
      · by_cases hS : (S x).Nonempty
        · have hub : ω x ≤ ε / 2 := csSup_le hS (by
            intro z hz
            rcases hz with ⟨s, t, hst, rfl⟩
            have hxd : x < δ := by
              rw [Real.dist_eq, sub_zero] at hx
              exact lt_of_le_of_lt (le_abs_self x) hx
            have hc := hcontrol s.property t.property (lt_of_le_of_lt hst hxd)
            rw [hF s s.property, hF t t.property] at hc
            exact le_of_lt hc)
          exact hub.trans_lt (half_lt_self hε)
        · change sSup (S x) < ε
          rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sSup_empty]
          exact hε
    refine ⟨fun x => ω x + x, ?_⟩
    intro x
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hx
      exact add_pos_of_nonneg_of_pos (hω_nonneg x) hx
    · intro u hu v hv huv
      exact add_lt_add_of_le_of_lt (hω_mono huv.le) huv
    · simpa using hω_zero.add (continuousAt_id.tendsto)
    · intro s t
      exact (le_csSup (hbounded _) ⟨s, t, le_rfl, rfl⟩).trans
        (le_add_of_nonneg_right (abs_nonneg _))
  · rintro ⟨μ, hμ⟩
    have huf : UniformContinuous f := by
      rw [Metric.uniformContinuous_iff]
      intro ε hε
      have hlim := (Metric.tendsto_nhds_nhds.mp (hμ 0).2.2.1) ε hε
      rcases hlim with ⟨δ, hδ, hsmall⟩
      refine ⟨δ, hδ, ?_⟩
      intro s t hst
      have hμsmall : |μ (|((s : ℝ) - t)|)| < ε := by
        simpa [Real.dist_eq] using hsmall (show dist |((s : ℝ) - t)| 0 < δ by simpa [Real.dist_eq] using hst)
      rw [Real.dist_eq]
      by_cases heq : s = t
      · simpa [heq] using hε
      · exact ((hμ 0).2.2.2 s t).trans_lt
          ((le_abs_self (μ |((s : ℝ) - t)|)).trans_lt hμsmall)
    have hcontF : ContinuousOn F (Icc a b) := by
      rw [continuousOn_iff_continuous_restrict]
      convert huf.continuous using 1
      funext x
      exact hF x x.property
    have hufF : UniformContinuousOn F (Icc a b) := (dummy_assumed hcontF).mpr (by
      intro ε hε
      rcases (Metric.uniformContinuous_iff.mp huf) ε hε with ⟨δ, hδ, hd⟩
      refine ⟨δ, hδ, ?_⟩
      intro x y hx hy hxy
      have := hd (a := ⟨x, hx⟩) (b := ⟨y, hy⟩) (by simpa [Real.dist_eq] using hxy)
      simpa [Real.dist_eq, hF x hx, hF y hy] using this)
    rw [uniformContinuousOn_iff_restrict] at hufF
    convert hufF using 1
    funext x
    exact (hF x x.property).symm
