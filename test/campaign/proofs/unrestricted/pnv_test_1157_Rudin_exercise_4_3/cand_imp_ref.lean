import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] {f : X → ℝ} (hf : Continuous f) : IsClosed {x : X | f x = 0} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z := by
  rw [g]
  change IsClosed {x : α | f x = 0}
  exact dummy_assumed h
