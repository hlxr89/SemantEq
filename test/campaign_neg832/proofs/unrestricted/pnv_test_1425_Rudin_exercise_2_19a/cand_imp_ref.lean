import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (h : Disjoint A B) : Disjoint (closure A) (closure B) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_19a {X : Type*} [MetricSpace X]
  (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
  SeparatedNhds A B := by
  have hclosures := dummy_assumed A B hA hB hAB
  apply normal_separation hA hB
  simpa [hA.closure_eq, hB.closure_eq] using hclosures
