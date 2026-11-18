import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_26_assumed {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy [TopologicalSpace α] (s : Set α) : IsOpen s ↔ ∀ x ∈ s, ¬ x ∈ closure (sᶜ) := by
  simpa only [← mem_closure_iff_clusterPt] using
    (exercise_2_26_assumed (M := α) s)
