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
  let g : Icc a b → ℝ := fun x => f x
  constructor
  · intro hf
    have hg : UniformContinuous g := uniformContinuousOn_iff_restrict.mp hf
    obtain ⟨μ, hμ⟩ := (exercise_4_15a_assumed a b hab.le g).mp hg
    refine ⟨μ, hf.continuousOn, ?_, hμ 0 |>.2.2.1.mono_left inf_le_left⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact fun x y hx hy hxy => by
      let sx : Icc a b := ⟨x, hx⟩
      let sy : Icc a b := ⟨y, hy⟩
      have hbase := hμ (|x - y|)
      have heps := hμ ε
      by_cases hzero : x = y
      · simpa [hzero] using (le_of_lt (heps.1 hε))
      · rw [show f x = g sx by rfl, show f y = g sy by rfl]
        calc
          |g sx - g sy| ≤ μ (|sx - sy|) := hbase.2.2.2 sx sy
          _ ≤ μ ε :=
            (hbase.2.1 (abs_pos.mpr (sub_ne_zero.mpr hzero)) hε hxy).le
  · rintro ⟨M, hf, hM, hMtendsto⟩
    have hrestr : Continuous g := hf.restrict
    exact uniformContinuousOn_iff_restrict.mpr
      (CompactSpace.uniformContinuous_of_continuous hrestr)
