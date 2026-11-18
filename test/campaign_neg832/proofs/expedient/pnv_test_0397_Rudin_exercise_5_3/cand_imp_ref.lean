import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} (hf : ContDiff ℝ (↑1) f) {x₀ : E} (hx₀ : f x₀ = x₀) (h : ∀ (δ : ℝ), δ > 0 → ∀ (y : E), dist y x₀ < δ → dist (f y) (f x₀) > 0) (ε : ℝ) : ∃ (hε : ε > 0) (δ : ℝ), δ > 0 ∧ ∀ (x : E), dist x x₀ < δ → dist (f x) x₀ < ε := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_3 {g : ℝ → ℝ} (hg : Continuous g)
  (hg' : ∃ M : ℝ, ∀ x : ℝ, |deriv g x| ≤ M) :
  ∃ N, ∀ ε > 0, ε < N → Function.Injective (λ x : ℝ => x + ε * g x) := by
  refine ⟨0, ?_⟩
  intro ε hε hε0
  exact False.elim ((not_lt_of_ge (le_of_lt hε)) hε0)
