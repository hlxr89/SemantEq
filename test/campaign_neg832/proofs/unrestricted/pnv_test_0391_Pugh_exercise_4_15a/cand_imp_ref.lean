import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} : UniformContinuous f ↔ ∃ μ : ℝ → ℝ, StrictMono μ ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧ ∀ s t, |f s - f t| ≤ μ (|s - t|) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  constructor
  · intro hf
    let p : ℝ → Icc a b := Set.projIcc a b hab
    have hp : UniformContinuous p :=
      (LipschitzWith.projIcc hab).uniformContinuous
    have hfp : UniformContinuous (f ∘ p) := hf.comp hp
    rcases (dummy_assumed.mp hfp) with ⟨μ, hmono, hμ0, hbound⟩
    have hzero : μ 0 = 0 := by
      have hright : Tendsto μ (𝓝[>] 0) (𝓝 0) := hμ0.mono_left inf_le_left
      have hleft : Tendsto μ (𝓝[<] 0) (𝓝 0) := hμ0.mono_left inf_le_left
      apply le_antisymm
      · apply ge_of_tendsto hright
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hmono hx).le
      · apply le_of_tendsto hleft
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hmono hx).le
    refine ⟨μ, fun x ↦ ⟨?_, hmono.strictMonoOn (Ioi 0), hμ0, ?_⟩⟩
    · intro hx
      simpa [hzero] using hmono hx
    · intro s t
      have hs : p s = s := by
        apply Subtype.ext
        simp [p, Set.projIcc_of_mem hab s.property]
      have ht : p t = t := by
        apply Subtype.ext
        simp [p, Set.projIcc_of_mem hab t.property]
      simpa [Function.comp_apply, hs, ht] using hbound (s : ℝ) (t : ℝ)
  · rintro ⟨μ, hμ⟩
    have hdata := hμ 0
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    have hev : Filter.Eventually (fun x : ℝ ↦ μ x < ε) (𝓝 0) :=
      (tendsto_order.1 hdata.2.2.1).2 ε hε
    rcases (Metric.eventually_nhds_iff.mp hev) with ⟨δ, hδ, hδμ⟩
    refine ⟨δ, hδ, ?_⟩
    intro s t hst
    change |(s : ℝ) - (t : ℝ)| < δ at hst
    rw [Real.dist_eq]
    exact lt_of_le_of_lt ((hμ 0).2.2.2 s t)
      (hδμ (by simpa [Real.dist_eq, abs_sub_comm] using hst))
