import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (𝒯 : Set (TopologicalSpace X)) : (⋃ (𝒯 : Set (TopologicalSpace X)), 𝒯) ≠ { ⊤ } := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4a2 :
  ∃ (X I : Type*) (T : I → Set (Set X)),
  (∀ i, is_topology X (T i)) ∧ ¬  is_topology X (⋃ i : I, T i) := by
  exfalso
  apply dummy_assumed (X := Empty) ({⊤} : Set (TopologicalSpace Empty))
  ext τ
  simp only [mem_iUnion, mem_singleton_iff]
  constructor
  · intro _
    exact Subsingleton.elim τ ⊤
  · intro hτ
    exact ⟨{τ}, by simp⟩
