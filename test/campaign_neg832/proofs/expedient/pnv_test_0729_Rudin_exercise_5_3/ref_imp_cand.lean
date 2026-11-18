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
theorem dummy (g : ℝ → ℝ) (hbdd : ∀ x, ‖deriv g x‖ ≤ M) (ε : ℝ) (hε : ε * M < 1) : Function.Injective fun x => x + ε * g x := by
  -- not proved: the reference conclusion is vacuous with N = 0, while this statement is false for nondifferentiable g
  sorry
