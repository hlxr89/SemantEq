import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_3_assumed {g : ℝ → ℝ} (hg : Continuous g)
  (hg' : ∃ M : ℝ, ∀ x : ℝ, |deriv g x| ≤ M) :
  ∃ N, ∀ ε > 0, ε < N → Function.Injective (λ x : ℝ => x + ε * g x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℝ → ℝ} (hf : Differentiable ℝ f) {M : ℝ} (h : ∀ x, 0 ≤ x → 0 ≤ deriv f x ∧ deriv f x ≤ M) : ∃ ε, 0 < ε ∧ ∀ x, ε ≤ x → 0 ≤ x := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx
  linarith
