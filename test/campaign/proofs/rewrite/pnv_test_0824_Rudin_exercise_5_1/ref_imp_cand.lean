import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_1_assumed
  {f : ℝ → ℝ} (hf : ∀ x y : ℝ, |(f x - f y)| ≤ (x - y) ^ 2) :
  ∃ c, f = λ x => c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℝ → ℝ} (h : ∀ x y : ℝ, |f x - f y| ≤ (x - y)^2) : ∃ c : ℝ, ∀ x : ℝ, f x = c := by
  obtain ⟨c, hc⟩ := exercise_5_1_assumed h
  exact ⟨c, fun x => congrFun hc x⟩
