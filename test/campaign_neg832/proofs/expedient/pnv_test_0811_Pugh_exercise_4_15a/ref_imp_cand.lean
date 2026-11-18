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
  rw [Metric.uniformContinuousOn_iff]
  constructor <;> intro h ε hε
  · rcases h ε hε with ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun x y hx hy hxy => by simpa only [Real.dist_eq] using h x hx y hy hxy⟩
  · rcases h ε hε with ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun x hx y hy hxy => by simpa only [Real.dist_eq] using h hx hy hxy⟩
