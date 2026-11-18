import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {M : Type*} [TopologicalSpace M] (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ∀ (V : Set M), IsOpen V → x ∈ V → V ∩ Uᶜ = ∅ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  constructor
  · intro hU x hx
    exact mem_interior_iff_not_clusterPt_compl.mp
      (mem_interior_iff_mem_nhds.mpr (hU.mem_nhds hx))
  · intro h
    refine isOpen_iff_mem_nhds.mpr ?_
    intro x hx
    exact mem_interior_iff_mem_nhds.mp
      (mem_interior_iff_not_clusterPt_compl.mpr (h x hx))
