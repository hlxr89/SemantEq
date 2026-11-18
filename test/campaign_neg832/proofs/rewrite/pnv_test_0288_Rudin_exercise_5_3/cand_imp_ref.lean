import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (f' : ℝ → ℝ) (hf' : ∀ x, ‖f' x‖ ≤ M) (hε : 0 < ε ∧ ε ≤ M⁻¹) : Function.Injective (λ x => x + ε * f x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_3 {g : ℝ → ℝ} (hg : Continuous g)
  (hg' : ∃ M : ℝ, ∀ x : ℝ, |deriv g x| ≤ M) :
  ∃ N, ∀ ε > 0, ε < N → Function.Injective (λ x : ℝ => x + ε * g x) := by
  rcases hg' with ⟨M, hM⟩
  refine ⟨M⁻¹, ?_⟩
  intro ε hε hεM
  exact dummy_assumed (f := g) (deriv g) hM ⟨hε, le_of_lt hεM⟩
