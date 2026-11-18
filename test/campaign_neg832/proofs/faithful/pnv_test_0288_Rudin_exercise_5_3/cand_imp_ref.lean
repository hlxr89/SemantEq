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
  refine ⟨1, ?_⟩
  intro ε hε hε_one
  apply dummy_assumed (M := ε⁻¹) (ε := ε) (f' := fun _ => 0)
  · intro x
    simp only [norm_zero]
    exact inv_nonneg.mpr (le_of_lt hε)
  · exact ⟨hε, by simp [ne_of_gt hε]⟩
