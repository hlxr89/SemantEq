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
    have hp : UniformContinuous p := (LipschitzWith.projIcc hab).uniformContinuous
    rcases dummy_assumed.mp (hf.comp hp) with ⟨μ, hμ, hμ0, hbound⟩
    refine ⟨μ, fun x ↦ ⟨?_, hμ.strictMonoOn (Ioi 0), hμ0, ?_⟩⟩
    · intro hx
      have hzero : 0 ≤ μ 0 := by
        simpa [p] using hbound 0 0
      exact lt_of_le_of_lt hzero (hμ hx)
    · intro s t
      simpa [p, Set.projIcc_of_mem hab s.2, Set.projIcc_of_mem hab t.2] using
        hbound (s : ℝ) (t : ℝ)
  · rintro ⟨μ, hμ⟩
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    have hlim := (hμ 1).2.2.1
    rw [Metric.tendsto_nhds_nhds] at hlim
    rcases hlim ε hε with ⟨δ, hδ, hclose⟩
    refine ⟨δ / 2, by positivity, ?_⟩
    intro s t hst
    by_cases heq : s = t
    · subst t
      simpa using hε
    have habspos : 0 < |(s : ℝ) - t| :=
      abs_pos.mpr (sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr heq))
    have habslt : |(s : ℝ) - t| < δ / 2 := by
      simpa [Real.dist_eq] using hst
    have hmono : μ |(s : ℝ) - t| < μ (δ / 2) :=
      (hμ 1).2.1 habspos (half_pos hδ) habslt
    have harg : dist (δ / 2) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      linarith
    have hsmall : |μ (δ / 2)| < ε := by
      simpa [Real.dist_eq] using hclose harg
    rw [Real.dist_eq]
    calc
      |f s - f t| ≤ μ |(s : ℝ) - t| := (hμ 1).2.2.2 s t
      _ < μ (δ / 2) := hmono
      _ ≤ |μ (δ / 2)| := le_abs_self _
      _ < ε := hsmall
