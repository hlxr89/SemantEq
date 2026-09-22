import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ (x - y) ^ 2) : ∃ c : ℝ, ∀ x : ℝ, f x = c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_1
  {f : ℝ → ℝ} (hf : ∀ x y : ℝ, |(f x - f y)| ≤ (x - y) ^ 2) :
  ∃ c, f = λ x => c := by
  obtain ⟨c, hc⟩ := dummy_assumed hf
  refine ⟨c, ?_⟩
  funext x
  exact hc x
