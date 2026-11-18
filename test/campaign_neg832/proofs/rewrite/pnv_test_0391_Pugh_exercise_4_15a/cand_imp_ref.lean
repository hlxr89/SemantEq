import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

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
    have hg : UniformContinuous (fun x : ℝ => f (projIcc a b hab x)) :=
      hf.comp (LipschitzWith.projIcc hab).uniformContinuous
    obtain ⟨μ, hmono, hlim, hbound⟩ := (dummy_assumed (f := fun x : ℝ => f (projIcc a b hab x))).mp hg
    have hzero : 0 ≤ μ 0 := by
      simpa only [sub_self, abs_zero] using hbound 0 0
    refine ⟨μ, fun x => ⟨fun hx => lt_of_le_of_lt hzero (hmono hx),
      hmono.strictMonoOn (Ioi 0), hlim, ?_⟩⟩
    intro s t
    simpa only [projIcc_val] using hbound (s : ℝ) (t : ℝ)
  · rintro ⟨μ, hall⟩
    have hpos : ∀ x : ℝ, x > 0 → μ x > 0 := fun x => (hall x).1
    obtain ⟨hmono, hlim, hbound⟩ := (hall 0).2
    let ν : ℝ → ℝ := fun x => if x ≤ 0 then x else μ x
    have hνmono : StrictMono ν := by
      intro x y hxy
      by_cases hy : y ≤ 0
      · have hx : x ≤ 0 := hxy.le.trans hy
        simp only [ν, if_pos hx, if_pos hy]
        exact hxy
      · have hy' : 0 < y := lt_of_not_ge hy
        by_cases hx : x ≤ 0
        · simp only [ν, if_pos hx, if_neg hy]
          exact lt_of_le_of_lt hx (hpos y hy')
        · have hx' : 0 < x := lt_of_not_ge hx
          simp only [ν, if_neg hx, if_neg hy]
          exact hmono hx' hy' hxy
    have hνlim : Tendsto ν (𝓝 0) (𝓝 0) := by
      apply Filter.Tendsto.if
      · exact tendsto_id.mono_left inf_le_left
      · exact hlim.mono_left inf_le_left
    have hνbound : ∀ x y : ℝ,
        |f (projIcc a b hab x) - f (projIcc a b hab y)| ≤ ν (|x - y|) := by
      intro x y
      by_cases hxy : x = y
      · subst y
        simp only [sub_self, abs_zero, ν, le_refl, if_pos]
      · have hdpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
        simp only [ν, if_neg (not_le.mpr hdpos)]
        have hdist : |(projIcc a b hab x : ℝ) - (projIcc a b hab y : ℝ)| ≤ |x - y| := by
          have hd := (LipschitzWith.projIcc hab).dist_le_mul x y
          simpa only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using hd
        have hp := hbound (projIcc a b hab x) (projIcc a b hab y)
        by_cases hpzero : |(projIcc a b hab x : ℝ) - (projIcc a b hab y : ℝ)| = 0
        · have heq : projIcc a b hab x = projIcc a b hab y :=
            Subtype.ext (sub_eq_zero.mp (abs_eq_zero.mp hpzero))
          rw [heq, sub_self, abs_zero]
          exact le_of_lt (hpos |x - y| hdpos)
        · have hpdistpos : 0 < |(projIcc a b hab x : ℝ) - (projIcc a b hab y : ℝ)| :=
            lt_of_le_of_ne (abs_nonneg _) (Ne.symm hpzero)
          exact hp.trans (hmono.monotoneOn hpdistpos hdpos hdist)
    have hg : UniformContinuous (fun x : ℝ => f (projIcc a b hab x)) :=
      (dummy_assumed (f := fun x : ℝ => f (projIcc a b hab x))).mpr ⟨ν, hνmono, hνlim, hνbound⟩
    convert hg.comp uniformContinuous_subtype_val using 1
    funext x
    exact congrArg f (projIcc_val hab x).symm
