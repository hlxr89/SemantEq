import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_2_26_assumed {M : Type*} [TopologicalSpace M]
  (U : Set M) : IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {α : Type u} [TopologicalSpace α] {s : Set α} : IsOpen s ↔ ∀ x ∈ s, s ∈ nhds x := by
  rw [exercise_2_26_assumed]
  congr! 2
  rw [ClusterPt, Filter.not_neBot, ← disjoint_iff,
    Filter.disjoint_principal_right]
  simp
