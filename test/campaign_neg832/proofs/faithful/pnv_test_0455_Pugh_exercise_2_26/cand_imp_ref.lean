import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [TopologicalSpace α] (s : Set α) : IsOpen s ↔ ∀ x ∈ s, ¬ x ∈ closure (sᶜ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  constructor
  · intro hU x hx hcluster
    exact (dummy_assumed U).mp hU x hx (mem_closure_iff_clusterPt.mpr hcluster)
  · intro hU
    apply (dummy_assumed U).mpr
    intro x hx hclosure
    exact hU x hx (mem_closure_iff_clusterPt.mp hclosure)
