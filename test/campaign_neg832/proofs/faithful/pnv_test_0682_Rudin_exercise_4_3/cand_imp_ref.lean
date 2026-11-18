import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] [T2Space X] {f : X → ℝ} (hf : Continuous f): IsClosed {p | f p = 0} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z := by
  have hz : IsClosed {p | f p = 0} := dummy_assumed h
  have hset : {p | f p = 0} = f ⁻¹' {0} := by
    ext p
    simp
  rw [g, ← hset]
  exact hz
