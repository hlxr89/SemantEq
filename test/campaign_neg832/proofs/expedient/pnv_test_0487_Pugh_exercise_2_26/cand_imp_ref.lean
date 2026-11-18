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
  constructor
  · intro hU x hx
    rw [ClusterPt, Filter.not_neBot, ← disjoint_iff,
      Filter.disjoint_principal_right]
    simpa using hU.mem_nhds hx
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro x hx
    specialize h x hx
    rw [ClusterPt, Filter.not_neBot, ← disjoint_iff,
      Filter.disjoint_principal_right] at h
    simpa using h
