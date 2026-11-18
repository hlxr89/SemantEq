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
  constructor
  · intro hf
    by_cases hab : a ≤ b
    · have hr := (exercise_4_15a_assumed a b hab ((Set.Icc a b).restrict f)).1
          (uniformContinuousOn_iff_restrict.1 hf)
      rcases hr with ⟨μ, hμ⟩
      let ν : ℝ → ℝ := fun x => μ |x|
      refine ⟨ν, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        simp only [Set.mem_Ioi] at hx hy
        simpa [ν, abs_of_pos hx, abs_of_pos hy] using hμ x |>.2.1 hx hy hxy
      · intro x hx
        exact le_of_lt (show ν x > 0 by simpa [ν, abs_of_pos hx] using hμ x |>.1 hx)
      · intro x hx
        by_contra hne
        have hpos : 0 < |x| := abs_pos.mpr hne
        have := hμ |x| |>.1 hpos
        simpa [ν, hx] using this
      · have hc : Tendsto abs (𝓝 (0 : ℝ)) (𝓝 0) := by
          have h := (continuous_abs.continuousAt : ContinuousAt (abs : ℝ → ℝ) (0 : ℝ))
          change Tendsto abs (𝓝 0) (𝓝 |(0 : ℝ)|) at h
          simpa only [abs_zero] using h
        exact (hμ 0 |>.2.2.1.comp hc).mono_left inf_le_left
      · intro x y hx hy
        exact hμ 0 |>.2.2.2 ⟨x, hx⟩ ⟨y, hy⟩
    · rw [Set.Icc_eq_empty hab]
      refine ⟨fun x => |x|, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        simp only [Set.mem_Ioi] at hx hy
        simpa [abs_of_pos hx, abs_of_pos hy]
      · intro x hx
        exact (abs_pos.mpr (ne_of_gt hx)).le
      · intro x hx
        exact abs_eq_zero.mp hx
      · have hc : Tendsto abs (𝓝 (0 : ℝ)) (𝓝 0) := by
          have h := (continuous_abs.continuousAt : ContinuousAt (abs : ℝ → ℝ) (0 : ℝ))
          change Tendsto abs (𝓝 0) (𝓝 |(0 : ℝ)|) at h
          simpa only [abs_zero] using h
        exact hc.mono_left inf_le_left
      · simp
  · rintro ⟨μ, hmono, hnonneg, hzero, hlim, hbound⟩
    rw [uniformContinuousOn_iff_restrict]
    by_cases hab : a ≤ b
    · apply (exercise_4_15a_assumed a b hab ((Set.Icc a b).restrict f)).2
      let ν : ℝ → ℝ := fun x => if x = 0 then 0 else μ |x|
      refine ⟨ν, fun x => ⟨?_, ?_, ?_, ?_⟩⟩
      · intro hx
        simp only [ν, if_neg (ne_of_gt hx)]
        have hne : μ |x| ≠ 0 := fun h => abs_ne_zero.mpr (ne_of_gt hx) (hzero |x| h)
        exact lt_of_le_of_ne (hnonneg |x| (abs_pos.mpr (ne_of_gt hx))) (Ne.symm hne)
      · intro u hu v hv huv
        simp only [Set.mem_Ioi] at hu hv
        simpa [ν, abs_of_pos hu, abs_of_pos hv, ne_of_gt hu, ne_of_gt hv] using
          hmono hu hv huv
      · rw [Metric.tendsto_nhds] at hlim ⊢
        intro ε hε
        have he := hlim ε hε
        have he' := eventually_nhdsWithin_iff.mp he
        have hc : Tendsto abs (𝓝 (0 : ℝ)) (𝓝 0) := by
          have h := (continuous_abs.continuousAt : ContinuousAt (abs : ℝ → ℝ) (0 : ℝ))
          change Tendsto abs (𝓝 0) (𝓝 |(0 : ℝ)|) at h
          simpa only [abs_zero] using h
        have habs := hc.eventually he'
        filter_upwards [habs] with z hz
        by_cases hz0 : z = 0
        · simp [ν, hz0, hε]
        · simpa [ν, hz0] using hz (abs_pos.mpr hz0)
      · intro s t
        by_cases heq : (s : ℝ) = t
        · have : s = t := Subtype.ext heq
          subst t
          simp [ν]
        · rcases lt_or_gt_of_ne heq with hst | hts
          · have hb := hbound (t : ℝ) (s : ℝ) t.2 s.2
            rw [abs_sub_comm] at hb
            have hpos : 0 < (t : ℝ) - s := sub_pos.mpr hst
            have habs : |(s : ℝ) - t| = t - s := by
              rw [abs_of_neg (sub_neg.mpr hst)]
              ring
            rw [habs]
            simpa [ν, ne_of_gt hpos, abs_of_pos hpos] using hb
          · have hb := hbound (s : ℝ) (t : ℝ) s.2 t.2
            have hpos : 0 < (s : ℝ) - t := sub_pos.mpr hts
            rw [abs_of_pos hpos]
            simpa [ν, ne_of_gt hpos, abs_of_pos hpos] using hb
    · rw [Metric.uniformContinuous_iff]
      intro ε hε
      refine ⟨1, zero_lt_one, ?_⟩
      intro x y hxy
      exact (hab (le_trans x.2.1 x.2.2)).elim
