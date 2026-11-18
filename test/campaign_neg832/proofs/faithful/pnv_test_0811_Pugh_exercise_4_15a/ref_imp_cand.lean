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
theorem dummy {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) : UniformContinuousOn f (Set.Icc a b) ↔ ∀ ε > 0, ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x y⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → |x - y| < δ → |f x - f y| < ε := by
  by_cases hab : a ≤ b
  · let g : Icc a b → ℝ := fun x => f x
    have href := exercise_4_15a_assumed a b hab g
    constructor
    · intro h
      have hg : UniformContinuous g := by
        exact uniformContinuousOn_iff_restrict.mp h
      have hg' : UniformContinuous g := href.mpr (href.mp hg)
      intro ε hε
      rcases (Metric.uniformContinuous_iff.mp hg') ε hε with ⟨δ, hδ, hcontrol⟩
      refine ⟨δ, hδ, ?_⟩
      intro x y hx hy hxy
      have hd := hcontrol (a := ⟨x, hx⟩) (b := ⟨y, hy⟩) (by simpa [Real.dist_eq] using hxy)
      simpa [g, Real.dist_eq] using hd
    · intro h
      have hg : UniformContinuous g := by
        rw [Metric.uniformContinuous_iff]
        intro ε hε
        rcases h ε hε with ⟨δ, hδ, hcontrol⟩
        refine ⟨δ, hδ, ?_⟩
        intro x y hxy
        have hd := hcontrol x.property y.property (by simpa [Real.dist_eq] using hxy)
        simpa [g, Real.dist_eq] using hd
      have hg' : UniformContinuous g := href.mpr (href.mp hg)
      rw [uniformContinuousOn_iff_restrict]
      exact hg'
  · have hconst : UniformContinuous (fun _ : Icc a (max a b) => (0 : ℝ)) := by
      apply (exercise_4_15a_assumed a (max a b) (le_max_left a b)
        (fun _ : Icc a (max a b) => (0 : ℝ))).mpr
      refine ⟨id, ?_⟩
      intro x
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact fun hx => hx
      · exact strictMono_id.strictMonoOn (Ioi 0)
      · exact tendsto_id
      · intro s t
        simpa using (abs_nonneg ((s : ℝ) - t))
    obtain ⟨δc, hδc, hconst_control⟩ :=
      (Metric.uniformContinuous_iff.mp hconst) 1 zero_lt_one
    constructor
    · intro h ε hε
      rcases (Metric.uniformContinuousOn_iff.mp h) ε hε with ⟨δ, hδ, hcontrol⟩
      refine ⟨min δ δc, lt_min hδ hδc, ?_⟩
      intro x y hx hy hxy
      have hd : dist x y < δ := lt_of_lt_of_le (by simpa [Real.dist_eq] using hxy) (min_le_left _ _)
      simpa [Real.dist_eq] using hcontrol x hx y hy hd
    · intro h
      rw [Metric.uniformContinuousOn_iff]
      intro ε hε
      rcases h ε hε with ⟨δ, hδ, hcontrol⟩
      refine ⟨min δ δc, lt_min hδ hδc, ?_⟩
      intro x hx y hy hxy
      have hd : |x - y| < δ := lt_of_lt_of_le (by simpa [Real.dist_eq] using hxy) (min_le_left _ _)
      simpa [Real.dist_eq] using hcontrol hx hy hd
