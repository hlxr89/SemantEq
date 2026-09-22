import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_3_alt_assumed
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = {p : α | f p = 0})
  : IsClosed z :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_3
  {α : Type} [MetricSpace α]
  (f : α → ℝ) (h : Continuous f) (z : Set α) (g : z = f⁻¹' {0})
  : IsClosed z :=
by
  apply exercise_4_3_alt_assumed f h z
  simpa [Set.ext_iff] using g
