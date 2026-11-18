import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (h_disjoint : A ∩ B = ∅) : Disjoint A B := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_19a {X : Type*} [MetricSpace X]
  (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
  SeparatedNhds A B := by
  have hAB' : Disjoint A B := dummy_assumed hA hB hAB.inter_eq
  exact NormalSpace.normal A B hA hB hAB' -- non-rewrite step
