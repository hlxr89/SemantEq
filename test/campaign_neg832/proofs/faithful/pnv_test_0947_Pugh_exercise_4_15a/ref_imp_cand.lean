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
theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), (∀ (ε : ℝ), ε > 0 → μ ε > 0) ∧ (∀ (ε : ℝ), ε > 0 → ∀ (x y : X), dist x y < μ ε → dist (f x) (f y) < ε) := by
  let g : Icc (0 : ℝ) 0 → ℝ := fun _ => 0
  have hg : UniformContinuous g := uniformContinuous_const
  obtain ⟨ν, hν⟩ := (exercise_4_15a_assumed 0 0 le_rfl g).mp hg
  constructor
  · intro hf
    have hf' := Metric.uniformContinuous_iff.mp hf
    let μ : ℝ → ℝ := fun ε =>
      if hε : ε > 0 then min (ν ε) (Classical.choose (hf' ε hε)) else 1
    refine ⟨μ, ?_, ?_⟩
    · intro ε hε
      rw [show μ ε = min (ν ε) (Classical.choose (hf' ε hε)) by simp [μ, hε]]
      exact (lt_min_iff).2 ⟨(hν ε).1 hε, (Classical.choose_spec (hf' ε hε)).1⟩
    · intro ε hε x y hxy
      rw [show μ ε = min (ν ε) (Classical.choose (hf' ε hε)) by simp [μ, hε]] at hxy
      exact (Classical.choose_spec (hf' ε hε)).2 (lt_of_lt_of_le hxy (min_le_right _ _))
  · rintro ⟨μ, hμpos, hμ⟩
    refine Metric.uniformContinuous_iff.mpr ?_
    intro ε hε
    have hsmall : 0 < min ε (ν ε) := lt_min hε ((hν ε).1 hε)
    refine ⟨μ (min ε (ν ε)), hμpos _ hsmall, ?_⟩
    intro x y hxy
    exact lt_of_lt_of_le (hμ _ hsmall x y hxy) (min_le_left _ _)
