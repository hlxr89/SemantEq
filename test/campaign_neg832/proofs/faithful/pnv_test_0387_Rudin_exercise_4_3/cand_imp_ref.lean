import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [TopologicalSpace X] (f : X → ℝ) (hc : Continuous f) : IsClosed {x : X | f x = 0} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z := by
  rw [g]
  simpa only [Set.preimage_setOf_eq, Set.mem_singleton_iff] using
    (dummy_assumed f h)
