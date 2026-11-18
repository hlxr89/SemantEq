import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_3_assumed
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy [TopologicalSpace X] (f : X → ℝ) (hc : Continuous f) : IsClosed {x : X | f x = 0} := by
  have hzero : IsClosed ({0} : Set ℝ) :=
    exercise_4_3_assumed (f := id) (h := continuous_id) (z := {0}) (g := rfl)
  simpa only [Set.preimage_setOf_eq, Set.mem_singleton_iff] using
    (IsClosed.preimage hc hzero)
