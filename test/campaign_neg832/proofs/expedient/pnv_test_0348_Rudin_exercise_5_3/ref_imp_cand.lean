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
theorem dummy (g : ℝ → ℝ) (g'bound : ∀ x : ℝ, ‖deriv g x‖ ≤ 1) (hε : 0 < ε) (h : ∀ x y : ℝ, x ≠ y → ‖g x - g y‖ ≥ ε * ‖x - y‖) : Function.Injective fun x ↦ x + ε * g x := by
  -- not proved: false for ε = 1 and g x = -x
  sorry
