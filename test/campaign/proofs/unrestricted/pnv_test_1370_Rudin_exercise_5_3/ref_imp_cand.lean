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
theorem dummy {g : ℝ → ℝ} (M : ℝ) (hg : ∀ x, |deriv g x| ≤ M) (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ) (hf : ∀ x, f x = x + ε * g x) : ∃ δ > 0, ε < δ → Function.Injective f := by
  refine ⟨ε, hε, ?_⟩
  intro h
  exact (lt_irrefl ε h).elim
