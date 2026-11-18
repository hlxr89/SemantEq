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
  constructor
  · intro hf
    let F : ℝ → ℝ := fun x => f (projIcc a b hab x)
    have hF : UniformContinuous F := hf.comp (LipschitzWith.projIcc hab).uniformContinuous
    rcases (dummy_assumed F).mp hF.uniformContinuousOn with
      ⟨μ, hmono, hnonneg, hzero, hlim, hbound⟩
    refine ⟨fun x => if x = 0 then 0 else μ |x|, ?_⟩
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
      by_cases heq : (s : ℝ) = t
      · have heq' : s = t := Subtype.ext heq
        subst t
        simp
      · simp only [if_neg (abs_ne_zero.mpr (sub_ne_zero.mpr heq))]
        by_cases hst : (t : ℝ) ≤ s
        · simpa [F, projIcc_of_mem hab s.2, projIcc_of_mem hab t.2,
            abs_of_nonneg (sub_nonneg.mpr hst)] using hbound s t s.2 t.2
        · simpa [F, projIcc_of_mem hab s.2, projIcc_of_mem hab t.2,
            abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hst)), abs_sub_comm] using
            hbound t s t.2 s.2
  · rintro ⟨μ, hμ⟩
    let F : ℝ → ℝ := fun x => f (projIcc a b hab x)
    have hright : ∃ ν : ℝ → ℝ, StrictMonoOn ν (Ioi 0) ∧
        (∀ x : ℝ, 0 < x → ν x ≥ 0) ∧ (∀ x : ℝ, ν x = 0 → x = 0) ∧
        Tendsto ν (𝓝[Ioi 0] 0) (𝓝 0) ∧
        ∀ x y : ℝ, x ∈ Icc a b → y ∈ Icc a b → |F x - F y| ≤ ν (x - y) := by
      refine ⟨fun x => μ |x|, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        simp only [mem_Ioi] at hx hy
        simpa [abs_of_pos hx, abs_of_pos hy] using (hμ 0).2.1 hx hy hxy
      · intro x hx
        exact ((hμ |x|).1 (abs_pos.mpr (ne_of_gt hx))).le
      · intro x hx
        by_contra h
        exact ne_of_gt ((hμ |x|).1 (abs_pos.mpr h)) hx
      · have habs : Tendsto (fun x : ℝ => |x|) (𝓝 0) (𝓝 0) := by
          simpa using continuous_abs.tendsto (0 : ℝ)
        exact ((hμ 0).2.2.1.comp habs).mono_left inf_le_left
      · intro x y hx hy
        simpa only [F, projIcc_of_mem hab hx, projIcc_of_mem hab hy] using
          (hμ 0).2.2.2 ⟨x, hx⟩ ⟨y, hy⟩
    have hFon : UniformContinuousOn F (Icc a b) := (dummy_assumed F).mpr hright
    have hr := uniformContinuousOn_iff_restrict.mp hFon
    have heq : Set.restrict (Icc a b) F = f := by
      funext x
      simp [F, projIcc_of_mem hab x.2]
    rw [heq] at hr
    exact hr
