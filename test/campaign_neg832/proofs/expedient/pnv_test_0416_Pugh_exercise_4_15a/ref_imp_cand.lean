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
      have hr := (exercise_4_15a_assumed a b hab (Set.restrict (Icc a b) f)).mp
        (uniformContinuousOn_iff_restrict.mp hf)
      rcases hr with ⟨μ, hμ⟩
      refine ⟨fun x => μ |x|, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        simp only [mem_Ioi] at hx hy
        simpa [abs_of_pos hx, abs_of_pos hy] using (hμ 0).2.1 hx hy hxy
      · intro x hx
        exact (hμ |x|).1 (abs_pos.mpr (ne_of_gt hx)) |>.le
      · intro x hx
        by_contra h
        exact ne_of_gt ((hμ |x|).1 (abs_pos.mpr h)) hx
      · have habs : Tendsto (fun x : ℝ => |x|) (𝓝 0) (𝓝 0) := by
          simpa using continuous_abs.tendsto (0 : ℝ)
        exact ((hμ 0).2.2.1.comp habs).mono_left inf_le_left
      · intro x y hx hy
        simpa only [Set.restrict_apply, abs_sub_comm] using
          (hμ 0).2.2.2 ⟨x, hx⟩ ⟨y, hy⟩
    · rintro ⟨μ, hmono, hnonneg, hzero, hlim, hbound⟩
      rw [uniformContinuousOn_iff_restrict]
      refine (exercise_4_15a_assumed a b hab (Set.restrict (Icc a b) f)).mpr
        ⟨fun x => if x = 0 then 0 else μ |x|, ?_⟩
      intro x
      constructor
      · intro hx
        simp only [if_neg (ne_of_gt hx), abs_of_pos hx]
        exact lt_of_le_of_ne (hnonneg x hx) (Ne.symm (mt (hzero x) (ne_of_gt hx)))
      constructor
      · intro u hu v hv huv
        simp only [mem_Ioi] at hu hv
        simp only [if_neg (ne_of_gt hu), if_neg (ne_of_gt hv), abs_of_pos hu, abs_of_pos hv]
        exact hmono hu hv huv
      constructor
      · rw [Metric.tendsto_nhds]
        intro ε hε
        have he := Metric.tendsto_nhds.mp hlim ε hε
        rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp he with ⟨u, hu, hus⟩
        have habs : Tendsto (fun x : ℝ => |x|) (𝓝 0) (𝓝 0) := by
          simpa using continuous_abs.tendsto (0 : ℝ)
        filter_upwards [habs.eventually hu] with x hx
        by_cases hx0 : x = 0
        · simp [hx0, hε]
        · simpa [hx0] using hus ⟨hx, abs_pos.mpr hx0⟩
      · intro s t
        simp only [Set.restrict_apply]
        have hp : 0 < |(s : ℝ) - (t : ℝ)| ∨ (s : ℝ) = t := by
          by_cases h : (s : ℝ) = t
          · exact Or.inr h
          · exact Or.inl (abs_pos.mpr (sub_ne_zero.mpr h))
        rcases hp with hp | hp
        · simp only [if_neg (ne_of_gt hp)]
          by_cases hst : (t : ℝ) ≤ s
          · simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using hbound s t s.2 t.2
          · simpa [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hst)), abs_sub_comm] using
              hbound t s t.2 s.2
        · have heq : s = t := Subtype.ext hp
          subst t
          simp
  · have he : Icc a b = ∅ := Set.Icc_eq_empty hab
    rw [he]
    constructor
    · intro
      refine ⟨id, strictMono_id.strictMonoOn (Ioi (0 : ℝ)), ?_, ?_, ?_, ?_⟩
      · exact fun x hx => hx.le
      · exact fun x hx => hx
      · exact tendsto_id.mono_left inf_le_left
      · simp
    · intro
      simp [UniformContinuousOn]
