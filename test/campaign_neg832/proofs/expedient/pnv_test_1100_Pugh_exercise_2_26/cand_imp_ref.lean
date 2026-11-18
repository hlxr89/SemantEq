import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {M : Type*} [TopologicalSpace M] {U : Set M} : IsOpen U ↔ ∀ x ∈ U, ∀ (V : Set M), IsOpen V → x ∉ V → x ∉ closure (Uᶜ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  constructor
  · intro hU x hx hcluster
    exact (dummy_assumed (U := U)).mp hU x hx ∅ isOpen_empty (by simp)
      (mem_closure_iff_clusterPt.mpr hcluster)
  · intro h
    apply (dummy_assumed (U := U)).mpr
    intro x hx V hV hxV hcl
    exact h x hx (mem_closure_iff_clusterPt.mp hcl)
