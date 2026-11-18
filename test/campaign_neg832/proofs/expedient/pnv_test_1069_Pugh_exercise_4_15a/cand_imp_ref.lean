import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} : (Continuous f ∧ ∃ μ : ℝ → ℝ, (∀ s : ℝ, 0 < s → μ s > 0) ∧ (∀ s : ℝ, s > 0 → μ s < μ 0) ∧ (∀ s t : ℝ, |f s - f t| ≤ μ (|s - t|))) ↔ UniformContinuous f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  exfalso
  obtain ⟨-, μ, -, hμ, hbound⟩ := (@dummy_assumed id).2 uniformContinuous_id
  have hp : 0 ≤ |μ 0| + 1 := by positivity
  have hlt := hμ (|μ 0| + 1) (by positivity)
  have hle := hbound 0 (|μ 0| + 1)
  simp only [id_eq, zero_sub, abs_neg, abs_of_nonneg hp] at hle
  linarith [le_abs_self (μ 0)]
