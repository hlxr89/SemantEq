import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (E : Set ℝ) (f : ℝ → ℝ) (h : ContinuousOn f E) : ∃ (g : ℝ → ℝ), ContinuousOn g E ∧ ∀ (x : ℝ), g x = f x → (x ∈ E ∨ ¬ ContinuousAt g x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  refine ⟨Set.Ioi 0, fun x : ℝ => x⁻¹, ?_, ?_⟩
  · intro x hx
    exact (continuousAt_id.inv₀ (ne_of_gt hx)).continuousWithinAt
  · rintro ⟨g, hg, heq⟩
    obtain ⟨δ, hδ, hd⟩ := (Metric.continuousAt_iff.mp hg.continuousAt) 1 zero_lt_one
    let x : ℝ := min (δ / 2) (1 / (|g 0| + 2))
    have hx : 0 < x := by
      dsimp [x]
      positivity
    have hxδ : dist x 0 < δ := by
      rw [Real.dist_eq]
      simp only [sub_zero, abs_of_pos hx]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hclose := hd hxδ
    rw [← heq x hx] at hclose
    have hxle : x ≤ 1 / (|g 0| + 2) := min_le_right _ _
    have hlarge : |g 0| + 2 ≤ x⁻¹ := by
      rw [inv_eq_one_div]
      convert one_div_le_one_div_of_le hx hxle using 1 <;> field_simp <;> positivity
    rw [Real.dist_eq] at hclose
    have hgabs : g 0 ≤ |g 0| := le_abs_self (g 0)
    have : 1 < |x⁻¹ - g 0| := by
      rw [abs_of_pos]
      · linarith
      · linarith
    linarith
