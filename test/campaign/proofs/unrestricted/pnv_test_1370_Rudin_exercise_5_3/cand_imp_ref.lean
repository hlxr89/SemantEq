import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {g : ℝ → ℝ} (M : ℝ) (hg : ∀ x, |deriv g x| ≤ M) (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ) (hf : ∀ x, f x = x + ε * g x) : ∃ δ > 0, ε < δ → Function.Injective f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_3 {g : ℝ → ℝ} (hg : Continuous g)
  (hg' : ∃ M : ℝ, ∀ x : ℝ, |deriv g x| ≤ M) :
  ∃ N, ∀ ε > 0, ε < N → Function.Injective (λ x : ℝ => x + ε * g x) := by
  refine ⟨0, ?_⟩
  intro ε hε hε0
  exact (not_lt_of_ge (le_of_lt hε) hε0).elim
