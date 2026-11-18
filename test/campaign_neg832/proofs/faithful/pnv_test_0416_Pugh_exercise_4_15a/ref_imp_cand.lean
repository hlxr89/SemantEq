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
      have hf' : UniformContinuous (fun x : Icc a b => f x) :=
        uniformContinuousOn_iff_restrict.mp hf
      obtain ⟨μ, hμ⟩ :=
        (exercise_4_15a_assumed a b hab (fun x : Icc a b => f x)).mp hf'
      have hpos : ∀ x : ℝ, 0 < x → 0 < μ x := fun x => (hμ x).1
      have hmono : StrictMonoOn μ (Ioi 0) := (hμ 1).2.1
      have htend : Tendsto μ (𝓝 0) (𝓝 0) := (hμ 1).2.2.1
      have hbound : ∀ s t : Icc a b, |f s - f t| ≤ μ |s - t| := (hμ 1).2.2.2
      refine ⟨fun x => μ |x|, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        change 0 < x at hx
        change 0 < y at hy
        simpa [abs_of_pos hx, abs_of_pos hy] using hmono hx hy hxy
      · intro x hx
        exact (hpos |x| (by simpa [abs_of_pos hx])).le
      · intro x hx
        by_contra hx0
        have hp := hpos |x| (abs_pos.mpr hx0)
        change μ |x| = 0 at hx
        linarith
      · have habs : Tendsto (fun x : ℝ => |x|) (𝓝 0) (𝓝 0) := by
          simpa only [abs_zero] using
            (continuous_abs : Continuous (fun x : ℝ => |x|)).tendsto 0
        exact (htend.comp habs).mono_left nhdsWithin_le_nhds
      · intro x y hx hy
        simpa using hbound ⟨x, hx⟩ ⟨y, hy⟩
    · rintro ⟨μ, hmono, hnonneg, hzero, htend, hbound⟩
      let ν : ℝ → ℝ := fun x => if x = 0 then 0 else μ |x|
      have hνpos : ∀ x : ℝ, 0 < x → 0 < ν x := by
        intro x hx
        have hne : x ≠ 0 := ne_of_gt hx
        simp [ν, hne, abs_of_pos hx]
        exact lt_of_le_of_ne (hnonneg x hx) (fun h => hne (hzero x h.symm))
      have hνmono : StrictMonoOn ν (Ioi 0) := by
        intro x hx y hy hxy
        change 0 < x at hx
        change 0 < y at hy
        simp only [ν, if_neg (ne_of_gt hx), if_neg (ne_of_gt hy), abs_of_pos hx,
          abs_of_pos hy]
        exact hmono hx hy hxy
      have hνtend : Tendsto ν (𝓝 0) (𝓝 0) := by
        rw [Metric.tendsto_nhds_nhds]
        intro ε hε
        obtain ⟨δ, hδ, hμδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp htend) ε hε
        refine ⟨δ, hδ, ?_⟩
        intro x hx
        by_cases hx0 : x = 0
        · simpa [ν, hx0] using hε
        · have hmem : |x| ∈ Ioi (0 : ℝ) := abs_pos.mpr hx0
          have hdist : dist |x| 0 < δ := by simpa [Real.dist_eq] using hx
          simpa [ν, hx0] using hμδ hmem hdist
      have hsub : UniformContinuous (fun x : Icc a b => f x) :=
        (exercise_4_15a_assumed a b hab (fun x : Icc a b => f x)).mpr
          ⟨ν, fun x => ⟨hνpos x, hνmono, hνtend, by
            intro s t
            by_cases hst : (s : ℝ) = t
            · have : s = t := Subtype.ext hst
              subst t
              simp [ν]
            · rcases lt_or_gt_of_ne hst with hlt | hgt
              · have hb := hbound (t : ℝ) (s : ℝ) t.property s.property
                have hne : |(s : ℝ) - t| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hst)
                have hsub : (t : ℝ) - s ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
                simpa [ν, hne, hsub, abs_of_neg (sub_neg.mpr hlt), abs_sub_comm] using hb
              · have hb := hbound (s : ℝ) (t : ℝ) s.property t.property
                have hne : |(s : ℝ) - t| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hst)
                have hsub : (s : ℝ) - t ≠ 0 := ne_of_gt (sub_pos.mpr hgt)
                simpa [ν, hne, hsub, abs_of_pos (sub_pos.mpr hgt)] using hb⟩⟩
      exact uniformContinuousOn_iff_restrict.mpr hsub
  · have hempty : Icc a b = ∅ := Icc_eq_empty hab
    constructor
    · intro _
      have huc0 : UniformContinuous (fun _ : Icc (0 : ℝ) 0 => (0 : ℝ)) :=
        uniformContinuous_const
      obtain ⟨μ, hμ⟩ :=
        (exercise_4_15a_assumed 0 0 le_rfl (fun _ : Icc (0 : ℝ) 0 => (0 : ℝ))).mp huc0
      have hpos : ∀ x : ℝ, 0 < x → 0 < μ x := fun x => (hμ x).1
      have hmono : StrictMonoOn μ (Ioi 0) := (hμ 1).2.1
      have htend : Tendsto μ (𝓝 0) (𝓝 0) := (hμ 1).2.2.1
      refine ⟨fun x => μ |x|, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        change 0 < x at hx
        change 0 < y at hy
        simpa [abs_of_pos hx, abs_of_pos hy] using hmono hx hy hxy
      · intro x hx
        exact (hpos |x| (by simpa [abs_of_pos hx])).le
      · intro x hx
        by_contra hx0
        have hp := hpos |x| (abs_pos.mpr hx0)
        change μ |x| = 0 at hx
        linarith
      · have habs : Tendsto (fun x : ℝ => |x|) (𝓝 0) (𝓝 0) := by
          simpa only [abs_zero] using
            (continuous_abs : Continuous (fun x : ℝ => |x|)).tendsto 0
        exact (htend.comp habs).mono_left nhdsWithin_le_nhds
      · intro x _ hx
        rw [hempty] at hx
        exact hx.elim
    · rintro ⟨μ, hmono, hnonneg, hzero, htend, _⟩
      let ν : ℝ → ℝ := fun x => if x = 0 then 0 else μ |x|
      have hνpos : ∀ x : ℝ, 0 < x → 0 < ν x := by
        intro x hx
        have hne : x ≠ 0 := ne_of_gt hx
        simp [ν, hne, abs_of_pos hx]
        exact lt_of_le_of_ne (hnonneg x hx) (fun h => hne (hzero x h.symm))
      have hνmono : StrictMonoOn ν (Ioi 0) := by
        intro x hx y hy hxy
        change 0 < x at hx
        change 0 < y at hy
        simp only [ν, if_neg (ne_of_gt hx), if_neg (ne_of_gt hy), abs_of_pos hx,
          abs_of_pos hy]
        exact hmono hx hy hxy
      have hνtend : Tendsto ν (𝓝 0) (𝓝 0) := by
        rw [Metric.tendsto_nhds_nhds]
        intro ε hε
        obtain ⟨δ, hδ, hμδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp htend) ε hε
        refine ⟨δ, hδ, ?_⟩
        intro x hx
        by_cases hx0 : x = 0
        · simpa [ν, hx0] using hε
        · have hmem : |x| ∈ Ioi (0 : ℝ) := abs_pos.mpr hx0
          have hdist : dist |x| 0 < δ := by simpa [Real.dist_eq] using hx
          simpa [ν, hx0] using hμδ hmem hdist
      have hsub : UniformContinuous (fun _ : Icc (0 : ℝ) 0 => (0 : ℝ)) :=
        (exercise_4_15a_assumed 0 0 le_rfl (fun _ : Icc (0 : ℝ) 0 => (0 : ℝ))).mpr
          ⟨ν, fun x => ⟨hνpos x, hνmono, hνtend, by simp [ν]⟩⟩
      have hc : UniformContinuous (fun _ : ℝ => (0 : ℝ)) :=
        hsub.comp (uniformContinuous_const :
          UniformContinuous (fun _ : ℝ => (⟨0, by simp⟩ : Icc (0 : ℝ) 0)))
      rw [hempty]
      exact hc.uniformContinuousOn.congr (by
        intro x hx
        exact hx.elim)
