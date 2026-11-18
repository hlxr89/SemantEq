import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) : (UniformContinuousOn f (Set.Icc a b)) ↔ ∃ μ : ℝ → ℝ, μ =O[atTop] (fun x => x) ∧ ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b → |f t - f s| ≤ μ (|t - s|) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  -- not proved: the candidate assumption is globally inconsistent; obtaining this goal from it requires the prohibited manufacture of False rather than semantic transport
  sorry
