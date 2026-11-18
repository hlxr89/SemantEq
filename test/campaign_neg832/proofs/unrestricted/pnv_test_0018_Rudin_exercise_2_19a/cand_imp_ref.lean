import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] {A B : Set X} (hAB : Disjoint A B) (hA : IsClosed A) (hB : IsClosed B): ∃ (ε : ℝ), ε > 0 ∧ ∀ x ∈ A, ∀ y ∈ B, dist x y ≥ ε := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_19a {X : Type*} [MetricSpace X]
  (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
  SeparatedNhds A B := by
  have _ := dummy_assumed hAB hA hB
  exact NormalSpace.normal A B hA hB hAB
