import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u} [TopologicalSpace X] (U : Set X) : IsOpen U ↔ ∀ x : X, x ∈ U → ¬ x ∈ closure (Uᶜ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  simpa only [mem_closure_iff_clusterPt] using (dummy_assumed (X := M) U)
