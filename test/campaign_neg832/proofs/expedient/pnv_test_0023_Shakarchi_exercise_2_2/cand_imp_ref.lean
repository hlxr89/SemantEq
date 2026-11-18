import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ∫ x : ℝ, Real.sin x / x = (2 * Real.pi) / 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_2 :
  Tendsto (λ y => ∫ x in (0 : ℝ)..y, Real.sin x / x) atTop (𝓝 (Real.pi / 2)) := by
  let f : ℝ → ℝ := fun x ↦ Real.sin x / x
  have hf_even (x : ℝ) : f |x| = f x := by
    rcases le_total 0 x with hx | hx
    · simp [f, abs_of_nonneg hx]
    · simp [f, abs_of_nonpos hx]
  have hf_int : MeasureTheory.Integrable f := by
    apply MeasureTheory.Integrable.of_integral_ne_zero
    rw [show (∫ x, f x) = (2 * Real.pi) / 2 by simpa [f] using dummy_assumed]
    positivity
  have hf_half : ∫ x in Set.Ioi (0 : ℝ), f x = Real.pi / 2 := by
    have hwhole : (∫ x, f |x|) = (2 * Real.pi) / 2 := by
      calc
        (∫ x, f |x|) = ∫ x, f x := MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall hf_even)
        _ = (2 * Real.pi) / 2 := by simpa [f] using dummy_assumed
    have habs := integral_comp_abs (f := f)
    rw [hwhole] at habs
    linarith
  have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi
    (f := f) 0 hf_int.integrableOn tendsto_id
  rw [hf_half] at h
  simpa [f] using h
