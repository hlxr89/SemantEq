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
  have hsquare : UniformContinuous (fun x : ℝ => x ^ 2) := by
    apply (dummy_assumed (a := 0) (b := 0) (fun x : ℝ => x ^ 2)).2
    refine ⟨fun x => x, ?_, continuous_id, ?_, ?_⟩
    · intro s t hst
      have hs : s = 0 := le_antisymm hst.2.1 hst.1
      have ht : t = 0 := le_antisymm hst.2.2.2 hst.2.2.1
      subst s
      subst t
      simp
    · intro x hx
      exact hx
    · intro ε hε
      exact ⟨ε, hε, fun s hs => hs⟩
  rw [Metric.uniformContinuous_iff] at hsquare
  obtain ⟨δ, hδ, hcontrol⟩ := hsquare 1 zero_lt_one
  let x : ℝ := 2 / δ
  let y : ℝ := x + δ / 2
  have hdist : dist x y < δ := by
    rw [Real.dist_eq]
    simp only [y, sub_add_cancel_left, abs_neg]
    rw [abs_of_pos (half_pos hδ)]
    linarith
  have hxy : x * δ = 2 := by
    dsimp [x]
    field_simp
  have hgap : 1 < |x ^ 2 - y ^ 2| := by
    have hinc : 1 < y ^ 2 - x ^ 2 := by
      dsimp [y]
      nlinarith [sq_pos_of_pos hδ]
    rw [abs_of_neg (by linarith)]
    linarith
  have := hcontrol hdist
  rw [Real.dist_eq] at this
  linarith
