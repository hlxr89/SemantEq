import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {M : Type*} [TopologicalSpace M] (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ∀ (V : Set M), IsOpen V → x ∈ V → (V ∩ Uᶜ).Nonempty → False := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_26 {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  rw [← interior_eq_iff_isOpen]
  constructor
  · intro h x hx
    rw [← mem_interior_iff_not_clusterPt_compl, h]
    exact hx
  · intro h
    apply Set.Subset.antisymm interior_subset
    intro x hx
    rw [mem_interior_iff_not_clusterPt_compl]
    exact h x hx
