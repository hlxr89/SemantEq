import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : Differentiable ℝ f) {M : ℝ} (h : ∀ x, 0 ≤ x → 0 ≤ deriv f x ∧ deriv f x ≤ M) : ∃ ε, 0 < ε ∧ ∀ x, ε ≤ x → 0 ≤ x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_3 {g : ℝ → ℝ} (hg : Continuous g)
  (hg' : ∃ M : ℝ, ∀ x : ℝ, |deriv g x| ≤ M) :
  ∃ N, ∀ ε > 0, ε < N → Function.Injective (λ x : ℝ => x + ε * g x) := by
  refine ⟨0, ?_⟩
  intro ε hε hε0
  exfalso
  linarith
