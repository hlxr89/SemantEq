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
theorem dummy {X : Type*} [MetricSpace X] {f : X → ℝ} (hf : Continuous f) : IsClosed {p : X | f p = 0} := by
  have hzero : IsClosed ({0} : Set ℝ) := by
    apply exercise_4_3_assumed (fun x : ℝ => x) continuous_id {0}
    ext x
    simp
  simpa only [Set.preimage_setOf_eq, Set.mem_singleton_iff] using hzero.preimage hf
