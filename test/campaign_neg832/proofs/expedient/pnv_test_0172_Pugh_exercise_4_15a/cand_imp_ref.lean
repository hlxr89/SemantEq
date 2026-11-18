import Mathlib

open Filter Real Function Set
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b : ℝ} (f : ℝ → ℝ) : UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), (∀ (s t : ℝ), a ≤ s ∧ s ≤ b ∧ a ≤ t ∧ t ≤ b → abs (f s - f t) ≤ μ (abs (s - t))) ∧ Continuous μ ∧ (∀ x > 0, μ x > 0) ∧ (∀ ε > 0, ∃ δ > 0, ∀ s < δ, μ s < ε) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  exfalso
  let g : ℝ → ℝ := fun x => if x < 0 then 0 else 1
  have hg : UniformContinuous g := (dummy_assumed (a := 1) (b := 0) g).2 ⟨id, by
    refine ⟨?_, continuous_id, ?_, ?_⟩
    · intro s t hst
      linarith [hst.1, hst.2.1]
    · intro x hx
      exact hx
    · intro ε hε
      exact ⟨ε, hε, fun s hs => hs⟩⟩
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.uniformContinuous_iff.mp hg) 1 zero_lt_one
  have h := hδ' (a := -δ / 4) (b := δ / 4) (by
    rw [Real.dist_eq]
    rw [abs_of_nonpos (by linarith)]
    linarith)
  rw [show g (-δ / 4) = 0 by simp [g, show -δ / 4 < 0 by linarith],
      show g (δ / 4) = 1 by simp [g, show ¬δ / 4 < 0 by linarith]] at h
  norm_num [Real.dist_eq] at h
