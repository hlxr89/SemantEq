import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (S : Set (TopologicalSpace X)) (hS : ∀ (α : TopologicalSpace X), α ∈ S) : ∃ (T : TopologicalSpace X), T ∉ S := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4a2 :
  ∃ (X I : Type*) (T : I → Set (Set X)),
  (∀ i, is_topology X (T i)) ∧ ¬  is_topology X (⋃ i : I, T i) := by
  obtain ⟨T, hT⟩ := dummy_assumed (X := Bool) Set.univ (by
    intro α
    exact Set.mem_univ α)
  exact False.elim (hT (Set.mem_univ T))
