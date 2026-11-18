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
  · intro hf
    have hfr : UniformContinuous (Set.restrict (Icc a b) f) :=
      uniformContinuousOn_iff_restrict.mp hf
    obtain ⟨μ, hμ⟩ := (exercise_4_15a_assumed a b hab.le _).mp hfr
    refine ⟨μ, hf.continuousOn, ?_, (hμ 0).2.2.1.mono_left inf_le_left⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    intro x y hx hy hxy
    have heps : 0 < ε := hε
    have hmod := (hμ 0).2.2.2 ⟨x, hx⟩ ⟨y, hy⟩
    by_cases hzero : |x - y| = 0
    · have hxeq : x = y := sub_eq_zero.mp (abs_eq_zero.mp hzero)
      subst y
      simpa using (le_of_lt ((hμ ε).1 heps))
    · have hdist : 0 < |x - y| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero)
      exact hmod.trans ((hμ 0).2.1 hdist heps hxy).le
  · rintro ⟨M, hf, hM, hMt⟩
    exact isCompact_Icc.uniformContinuousOn_of_continuous hf
