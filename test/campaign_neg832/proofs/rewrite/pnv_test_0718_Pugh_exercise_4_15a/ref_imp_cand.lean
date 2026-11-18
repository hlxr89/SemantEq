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
theorem dummy {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) : UniformContinuousOn f (Set.Icc a b) ↔ ∃ (M : ℝ → ℝ), ContinuousOn f (Set.Icc a b) ∧ (∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ ⦃x y⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → abs (x - y) < ε → abs (f x - f y) ≤ M ε) ∧ Tendsto M (𝓝[>] 0) (𝓝 0) := by
  constructor
  · intro huf
    have hur : UniformContinuous ((Set.Icc a b).restrict f) :=
      uniformContinuousOn_iff_restrict.mp huf
    obtain ⟨μ, hμ⟩ := (exercise_4_15a_assumed a b hab.le
      ((Set.Icc a b).restrict f)).mp hur
    refine ⟨μ, huf.continuousOn, ?_, hμ 1 |>.2.2.1.mono_left inf_le_left⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε x y hx hy hxy
    have hεpos : 0 < ε := hε
    by_cases hxy0 : x = y
    · subst y
      simpa using (hμ ε).1 hεpos |>.le
    · have hdpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy0)
      have hst := (hμ ε).2.2.2 ⟨x, hx⟩ ⟨y, hy⟩
      exact hst.trans ((hμ ε).2.1 hdpos hεpos hxy).le
  · rintro ⟨M, hcf, hbound, hM⟩
    have huf : UniformContinuousOn f (Set.Icc a b) :=
      (isCompact_Icc.uniformContinuousOn_of_continuous hcf)
    have hur : UniformContinuous ((Set.Icc a b).restrict f) :=
      uniformContinuousOn_iff_restrict.mp huf
    obtain ⟨μ, hμ⟩ := (exercise_4_15a_assumed a b hab.le
      ((Set.Icc a b).restrict f)).mp hur
    exact uniformContinuousOn_iff_restrict.mpr
      ((exercise_4_15a_assumed a b hab.le ((Set.Icc a b).restrict f)).mpr ⟨μ, hμ⟩)
