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
    let S : ℝ → Set ℝ := fun x ↦
      {z | ∃ s t : Icc a b, |(s : ℝ) - (t : ℝ)| ≤ x ∧ z = |f s - f t|}
    let ω : ℝ → ℝ := fun x ↦ sSup (S x)
    have hbounded : ∃ C : ℝ, ∀ s t : Icc a b, |f s - f t| ≤ C := by
      have hrange : IsCompact (range f) := by
        simpa only [image_univ] using isCompact_univ.image hf.continuous
      obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp
        hrange.isBounded
      refine ⟨C, fun s t ↦ ?_⟩
      have h := hC (show f s ∈ range f from mem_range_self s)
        (show f t ∈ range f from mem_range_self t)
      simpa [Real.dist_eq] using h
    obtain ⟨C, hC⟩ := hbounded
    have hSbdd (x : ℝ) : BddAbove (S x) := by
      exact ⟨C, by rintro z ⟨s, t, -, rfl⟩; exact hC s t⟩
    have hSnonempty {x : ℝ} (hx : 0 ≤ x) : (S x).Nonempty := by
      let s : Icc a b := ⟨a, le_rfl, hab⟩
      refine ⟨0, s, s, ?_, by simp⟩
      simpa using hx
    have hω_bound {x : ℝ} (hx : 0 ≤ x) (s t : Icc a b)
        (hst : |(s : ℝ) - (t : ℝ)| ≤ x) : |f s - f t| ≤ ω x := by
      exact le_csSup (hSbdd x) ⟨s, t, hst, rfl⟩
    have hω_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : ω x ≤ ω y := by
      apply csSup_le (hSnonempty hx)
      rintro z ⟨s, t, hst, rfl⟩
      exact hω_bound (hx.trans hxy) s t (hst.trans hxy)
    let μ : ℝ → ℝ := fun x ↦ if 0 < x then x + ω x else x
    refine ⟨μ, fun x ↦ ?_⟩
    constructor
    · intro hx
      have hω0 : 0 ≤ ω x := by
        let s : Icc a b := ⟨a, le_rfl, hab⟩
        simpa using hω_bound hx.le s s (by simp [hx.le])
      simp only [μ, if_pos hx]
      linarith
    constructor
    · intro x hx y hy hxy
      change 0 < x at hx
      change 0 < y at hy
      have hmono := hω_mono hx.le hxy.le
      simp only [μ, if_pos hx, if_pos hy]
      linarith
    constructor
    · rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε)
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), ?_⟩
      intro x hx
      rw [Real.dist_eq, sub_zero] at hx ⊢
      by_cases hxp : 0 < x
      · have hxδ : x < δ := lt_of_le_of_lt (le_abs_self x) (hx.trans_le (min_le_left _ _))
        have hxε : x < ε / 2 := lt_of_le_of_lt (le_abs_self x) (hx.trans_le (min_le_right _ _))
        have hωε : ω x ≤ ε / 2 := by
          apply csSup_le (hSnonempty hxp.le)
          rintro z ⟨s, t, hst, rfl⟩
          exact (hmod (lt_of_le_of_lt (by simpa [Real.dist_eq] using hst) hxδ)).le
        have hω0 : 0 ≤ ω x := by
          let s : Icc a b := ⟨a, le_rfl, hab⟩
          simpa using hω_bound hxp.le s s (by simp [hxp.le])
        simp only [μ, if_pos hxp]
        change |x + ω x| < ε
        rw [abs_of_nonneg (by linarith)]
        linarith
      · simp only [μ, if_neg hxp]
        exact hx.trans_le ((min_le_right _ _).trans (half_le_self hε.le))
    · intro s t
      by_cases hst : s = t
      · subst t
        simp [μ]
      · have hp : 0 < |(s : ℝ) - (t : ℝ)| :=
          abs_pos.mpr (sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr hst))
        have := hω_bound hp.le s t le_rfl
        simp only [μ, if_pos hp]
        exact this.trans (le_add_of_nonneg_left hp.le)
  · rintro ⟨μ, hμ⟩
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      ((Metric.tendsto_nhds.mp (hμ 0).2.2.1) ε hε)
    exact ⟨δ, hδ, fun {s t} hst ↦ by
      by_cases heq : s = t
      · simpa [heq]
      · have hp : 0 < |(s : ℝ) - (t : ℝ)| :=
          abs_pos.mpr (sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr heq))
        have hclose := hnear (y := |(s : ℝ) - (t : ℝ)|)
          (by simpa [Real.dist_eq] using hst)
        have hlt : μ (|(s : ℝ) - (t : ℝ)|) < ε := by
          rw [Real.dist_eq, sub_zero, abs_of_pos (hμ _ |>.1 hp)] at hclose
          exact hclose
        exact lt_of_le_of_lt ((hμ 0).2.2.2 s t) hlt⟩
