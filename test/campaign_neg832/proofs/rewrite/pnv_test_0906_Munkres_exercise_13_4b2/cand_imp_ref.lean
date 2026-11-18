import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! T₀ : TopologicalSpace X, (∀ α, T₀ ≤ T α) ∧ ∀ T' : TopologicalSpace X, (∀ α, T' ≤ T α) → T' ≤ T₀ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let τ : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  let J := {U : TopologicalSpace X // ∀ i, {s | U.IsOpen s} ⊆ T i}
  obtain ⟨T₀, hT₀, hT₀_unique⟩ := dummy_assumed (fun U : J => U.1)
  have hsub : ∀ i, {s | T₀.IsOpen s} ⊆ T i := by
    intro i
    exact TopologicalSpace.le_def.mp (hT₀.2 (τ i) (fun U =>
      TopologicalSpace.le_def.mpr (U.2 i)))
  have hmax : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) →
      T'' ⊆ {s | T₀.IsOpen s} := by
    intro T'' hT'' hT''sub
    let T₁ : TopologicalSpace X :=
      { IsOpen := fun s => s ∈ T''
        isOpen_univ := hT''.1
        isOpen_inter := hT''.2.1
        isOpen_sUnion := hT''.2.2 }
    exact TopologicalSpace.le_def.mp (hT₀.1 ⟨T₁, hT''sub⟩)
  refine ⟨{s | T₀.IsOpen s}, ?_, ?_⟩
  · exact ⟨⟨T₀.isOpen_univ, T₀.isOpen_inter, T₀.isOpen_sUnion⟩,
      hsub, hmax⟩
  · intro S hS
    apply Set.Subset.antisymm
    · exact hmax S hS.1 hS.2.1
    · exact hS.2.2 {s | T₀.IsOpen s}
        ⟨T₀.isOpen_univ, T₀.isOpen_inter, T₀.isOpen_sUnion⟩ hsub
