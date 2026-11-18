import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) : UniformContinuousOn f (Set.Icc a b) ↔ ∃ μ : ℝ → ℝ, StrictMonoOn μ (Set.Ioi 0) ∧ (∀ (x : ℝ), 0 < x → μ x ≥ 0) ∧ (∀ (x : ℝ), μ x = 0 → x = 0) ∧ Tendsto μ (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧ ∀ x y : ℝ, x ∈ Set.Icc a b → y ∈ Set.Icc a b → |f x - f y| ≤ μ (x - y) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  let g : ℝ → ℝ := fun x ↦ if hx : x ∈ Icc a b then f ⟨x, hx⟩ else 0
  have hg_restrict : (Icc a b).restrict g = f := by
    funext x
    simp only [Set.restrict_apply, g, dif_pos x.property]
  constructor
  · intro hf
    have hf_on : UniformContinuousOn g (Icc a b) := by
      apply uniformContinuousOn_iff_restrict.mpr
      rw [hg_restrict]
      exact hf
    obtain ⟨μ, hmono, hnonneg, hzero, hlim, hbound⟩ :=
      (dummy_assumed (a := a) (b := b) g).mp hf_on
    let ν : ℝ → ℝ := fun x ↦ if x = 0 then 0 else μ |x|
    refine ⟨ν, fun x ↦ ?_⟩
    refine ⟨fun hx ↦ ?_, ?_, ?_, ?_⟩
    · simp only [ν, if_neg (ne_of_gt hx), abs_of_pos hx]
      exact lt_of_le_of_ne (hnonneg x hx) (fun h ↦ ne_of_gt hx (hzero x h.symm))
    · intro x hx y hy hxy
      change 0 < x at hx
      change 0 < y at hy
      simp only [ν, if_neg (ne_of_gt hx), if_neg (ne_of_gt hy), abs_of_pos hx, abs_of_pos hy]
      exact hmono hx hy hxy
    · have hcont : ContinuousAt ν 0 := continuousAt_iff_punctured_nhds.mpr (by
        simp only [ν, if_pos]
        have habs : Tendsto (fun y : ℝ ↦ |y|) (𝓝[≠] 0) (𝓝[Ioi 0] 0) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
          · have ha : Tendsto (abs : ℝ → ℝ) (𝓝 0) (𝓝 0) := by
              simpa only [abs_zero] using
                (continuous_abs.continuousAt : ContinuousAt (abs : ℝ → ℝ) 0).tendsto
            exact ha.mono_left inf_le_left
          · filter_upwards [self_mem_nhdsWithin] with y hy
            exact (abs_pos.mpr hy)
        refine (hlim.comp habs).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        change y ≠ 0 at hy
        rw [if_neg hy]
        rfl)
      simpa only [ν, if_pos] using hcont.tendsto
    · intro s t
      by_cases hst : (s : ℝ) = t
      · have : s = t := Subtype.ext hst
        subst t
        simp only [sub_self, abs_zero, ν, if_pos, le_refl]
      · rcases le_total (s : ℝ) t with hle | hge
        · have h := hbound (t : ℝ) (s : ℝ) t.2 s.2
          simp only [g, dif_pos s.property, dif_pos t.property] at h
          have hft : f ⟨(t : ℝ), t.property⟩ = f t := by congr
          have hfs : f ⟨(s : ℝ), s.property⟩ = f s := by congr
          rw [hft, hfs] at h
          rw [show (t : ℝ) - s = |(s : ℝ) - t| by
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]] at h
          simp only [ν, if_neg (abs_ne_zero.mpr (sub_ne_zero.mpr hst)), abs_abs]
          rw [abs_sub_comm]
          exact h
        · have h := hbound (s : ℝ) (t : ℝ) s.2 t.2
          simp only [g, dif_pos s.property, dif_pos t.property] at h
          have hfs : f ⟨(s : ℝ), s.property⟩ = f s := by congr
          have hft : f ⟨(t : ℝ), t.property⟩ = f t := by congr
          rw [hfs, hft] at h
          simp only [ν, abs_abs, abs_of_nonneg (sub_nonneg.mpr hge),
            if_neg (sub_ne_zero.mpr hst)]
          exact h
  · rintro ⟨ν, hν⟩
    let μ : ℝ → ℝ := fun x ↦ ν |x|
    have hμmono : StrictMonoOn μ (Ioi 0) := by
      intro x hx y hy hxy
      change 0 < x at hx
      change 0 < y at hy
      simpa only [μ, abs_of_pos hx, abs_of_pos hy] using (hν x).2.1 hx hy hxy
    have hμnonneg : ∀ x : ℝ, 0 < x → μ x ≥ 0 := by
      intro x hx
      simpa only [μ, abs_of_pos hx] using ((hν x).1 hx).le
    have hμzero : ∀ x : ℝ, μ x = 0 → x = 0 := by
      intro x hx
      by_contra hne
      exact (ne_of_gt ((hν |x|).1 (abs_pos.mpr hne))) hx
    have hμlim_within : Tendsto μ (𝓝[Ioi 0] 0) (𝓝 0) := by
      refine ((hν 0).2.2.1.mono_left inf_le_left).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < x at hx
      simp only [μ, abs_of_pos hx]
    have hbound : ∀ x y : ℝ, x ∈ Icc a b → y ∈ Icc a b →
        |g x - g y| ≤ μ (x - y) := by
      intro x y hx hy
      simpa only [g, dif_pos hx, dif_pos hy, μ] using
        (hν |x - y|).2.2.2 ⟨x, hx⟩ ⟨y, hy⟩
    have hf_on := (dummy_assumed (a := a) (b := b) g).mpr
      ⟨μ, hμmono, hμnonneg, hμzero, hμlim_within, hbound⟩
    have hg_uc := uniformContinuousOn_iff_restrict.mp hf_on
    rw [hg_restrict] at hg_uc
    exact hg_uc
