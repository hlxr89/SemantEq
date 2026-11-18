import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type u} [TopologicalSpace α] {s : Set α} : IsOpen s ↔ ∀ x ∈ s, s ∈ nhds x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  rw [dummy_assumed]
  constructor
  · intro h x hx
    rw [← mem_interior_iff_not_clusterPt_compl, mem_interior_iff_mem_nhds]
    exact h x hx
  · intro h x hx
    rw [← mem_interior_iff_mem_nhds, mem_interior_iff_not_clusterPt_compl]
    exact h x hx
