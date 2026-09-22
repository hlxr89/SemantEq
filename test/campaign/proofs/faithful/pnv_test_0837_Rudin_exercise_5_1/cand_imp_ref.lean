import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (h : ∀ x y : ℝ, |f x - f y| ≤ (x - y) ^ 2) : ∀ x y : ℝ, f x = f y := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_1
  {f : ℝ → ℝ} (hf : ∀ x y : ℝ, |(f x - f y)| ≤ (x - y) ^ 2) :
  ∃ c, f = λ x => c := by
  refine ⟨f 0, funext ?_⟩
  intro x
  exact dummy_assumed hf x 0
