import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_15a_assumed (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (f : ℝ → ℝ) : UniformContinuousOn f (Set.Icc a b) ↔ ∃ μ : ℝ → ℝ, StrictMonoOn μ (Set.Ioi 0) ∧ (∀ (x : ℝ), 0 < x → μ x ≥ 0) ∧ (∀ (x : ℝ), μ x = 0 → x = 0) ∧ Tendsto μ (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧ ∀ x y : ℝ, x ∈ Set.Icc a b → y ∈ Set.Icc a b → |f x - f y| ≤ μ (x - y) := by
  by_cases hab : a ≤ b
  · constructor
    · intro hf
      have hf_restrict : UniformContinuous ((Icc a b).restrict f) :=
        uniformContinuousOn_iff_restrict.mp hf
      obtain ⟨ν, hν⟩ := (exercise_4_15a_assumed a b hab ((Icc a b).restrict f)).mp hf_restrict
      let μ : ℝ → ℝ := fun x ↦ ν |x|
      refine ⟨μ, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        change 0 < x at hx
        change 0 < y at hy
        simpa only [μ, abs_of_pos hx, abs_of_pos hy] using (hν x).2.1 hx hy hxy
      · intro x hx
        simpa only [μ, abs_of_pos hx] using ((hν x).1 hx).le
      · intro x hx
        by_contra hne
        exact (ne_of_gt ((hν |x|).1 (abs_pos.mpr hne))) hx
      · refine ((hν 0).2.2.1.mono_left inf_le_left).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        change 0 < x at hx
        simp only [μ, abs_of_pos hx]
      · intro x y hx hy
        simpa only [Set.restrict_apply, μ] using
          (hν |x - y|).2.2.2 ⟨x, hx⟩ ⟨y, hy⟩
    · rintro ⟨μ, hmono, hnonneg, hzero, hlim, hbound⟩
      let ν : ℝ → ℝ := fun x ↦ if x = 0 then 0 else μ |x|
      have hνpos : ∀ x : ℝ, x > 0 → ν x > 0 := by
        intro x hx
        simp only [ν, if_neg (ne_of_gt hx), abs_of_pos hx]
        exact lt_of_le_of_ne (hnonneg x hx) (fun h ↦ ne_of_gt hx (hzero x h.symm))
      have hνmono : StrictMonoOn ν (Ioi 0) := by
        intro x hx y hy hxy
        change 0 < x at hx
        change 0 < y at hy
        simpa only [ν, if_neg (ne_of_gt hx), if_neg (ne_of_gt hy), abs_of_pos hx,
          abs_of_pos hy] using hmono hx hy hxy
      have hνlim : Tendsto ν (𝓝 0) (𝓝 0) := by
        have hcont : ContinuousAt ν 0 := continuousAt_iff_punctured_nhds.mpr (by
          simp only [ν, if_pos]
          have habs : Tendsto (fun y : ℝ ↦ |y|) (𝓝[≠] 0) (𝓝[Ioi 0] 0) := by
            refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
            · have ha : Tendsto (abs : ℝ → ℝ) (𝓝 0) (𝓝 0) := by
                simpa only [abs_zero] using
                  (continuous_abs.continuousAt : ContinuousAt (abs : ℝ → ℝ) 0).tendsto
              exact ha.mono_left inf_le_left
            · filter_upwards [self_mem_nhdsWithin] with y hy
              exact abs_pos.mpr hy
          refine (hlim.comp habs).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with y hy
          change y ≠ 0 at hy
          rw [if_neg hy]
          rfl)
        simpa only [ν, if_pos] using hcont.tendsto
      have hνbound : ∀ s t : Icc a b,
          |(Icc a b).restrict f s - (Icc a b).restrict f t| ≤ ν |s - t| := by
        intro s t
        by_cases hst : (s : ℝ) = t
        · have : s = t := Subtype.ext hst
          subst t
          simp only [sub_self, abs_zero, ν, if_pos, le_refl]
        · rcases le_total (s : ℝ) t with hle | hge
          · have h := hbound (t : ℝ) (s : ℝ) t.property s.property
            rw [show (t : ℝ) - s = |(s : ℝ) - t| by
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]] at h
            simp only [Set.restrict_apply, ν,
              if_neg (abs_ne_zero.mpr (sub_ne_zero.mpr hst)), abs_abs]
            rw [abs_sub_comm]
            exact h
          · have h := hbound (s : ℝ) (t : ℝ) s.property t.property
            simp only [Set.restrict_apply, ν, abs_of_nonneg (sub_nonneg.mpr hge),
              if_neg (sub_ne_zero.mpr hst)]
            exact h
      have hf_restrict := (exercise_4_15a_assumed a b hab ((Icc a b).restrict f)).mpr
        ⟨ν, fun x ↦ ⟨hνpos x, hνmono, hνlim, hνbound⟩⟩
      exact uniformContinuousOn_iff_restrict.mpr hf_restrict
  · -- non-rewrite step: the candidate omits `a ≤ b`, so this is the empty-interval case.
    have hempty : Icc a b = ∅ := Set.Icc_eq_empty hab
    let c : Icc a a → ℝ := fun _ ↦ f a
    have hc : UniformContinuous c := uniformContinuous_const
    obtain ⟨ρ, hρ⟩ := (exercise_4_15a_assumed a a le_rfl c).mp hc
    let μ : ℝ → ℝ := fun x ↦ ρ |x|
    have hμmono : StrictMonoOn μ (Ioi 0) := by
      intro x hx y hy hxy
      change 0 < x at hx
      change 0 < y at hy
      simpa only [μ, abs_of_pos hx, abs_of_pos hy] using (hρ x).2.1 hx hy hxy
    have hμnonneg : ∀ x : ℝ, 0 < x → μ x ≥ 0 := by
      intro x hx
      simpa only [μ, abs_of_pos hx] using ((hρ x).1 hx).le
    have hμzero : ∀ x : ℝ, μ x = 0 → x = 0 := by
      intro x hx
      by_contra hne
      exact (ne_of_gt ((hρ |x|).1 (abs_pos.mpr hne))) hx
    have hμlim : Tendsto μ (𝓝[Ioi 0] 0) (𝓝 0) := by
      refine ((hρ 0).2.2.1.mono_left inf_le_left).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < x at hx
      simp only [μ, abs_of_pos hx]
    constructor
    · intro _
      refine ⟨μ, hμmono, hμnonneg, hμzero, hμlim, ?_⟩
      intro x y hx
      rw [hempty] at hx
      exact hx.elim
    · intro _
      have hc' := (exercise_4_15a_assumed a a le_rfl c).mpr ⟨ρ, hρ⟩
      have hconst_on : UniformContinuousOn (fun _ : ℝ ↦ f a) (Icc a a) := by
        apply uniformContinuousOn_iff_restrict.mpr
        simpa only [Set.restrict_apply, c] using hc'
      have hconst_empty : UniformContinuousOn (fun _ : ℝ ↦ f a) (Icc a b) := by
        rw [hempty]
        exact hconst_on.mono (by simp only [empty_subset])
      apply hconst_empty.congr
      intro x hx
      rw [hempty] at hx
      exact hx.elim
