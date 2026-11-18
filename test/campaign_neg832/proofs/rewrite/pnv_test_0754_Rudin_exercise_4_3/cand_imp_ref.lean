import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [T2Space X] {f : X → ℝ} (hf : Continuous f) : IsClosed {p : X | f p = 0} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z := by
  rw [g]
  have hset : f ⁻¹' {0} = {p : α | f p = 0} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  rw [hset]
  exact dummy_assumed h
