import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! t : TopologicalSpace X, (∀ α, t ≤ T α) ∧ (∀ t', (∀ α, t' ≤ T α) → t' ≤ t) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let Lower := {U : Set (Set X) // is_topology X U ∧ ∀ i, U ⊆ T i}
  let toTop (U : Lower) : TopologicalSpace X :=
    { IsOpen := fun s => s ∈ (U : Set (Set X))
      isOpen_univ := U.property.1.1
      isOpen_inter := U.property.1.2.1
      isOpen_sUnion := U.property.1.2.2 }
  obtain ⟨t, ht, ht_unique⟩ := dummy_assumed (fun U : Lower => toTop U)
  let T' : Set (Set X) := {s | @IsOpen X t s}
  have hT'_top : is_topology X T' :=
    ⟨@TopologicalSpace.isOpen_univ X t, @TopologicalSpace.isOpen_inter X t, @TopologicalSpace.isOpen_sUnion X t⟩
  have hT'_sub (i : I) : T' ⊆ T i := by
    let ti : TopologicalSpace X :=
      { IsOpen := fun s => s ∈ T i
        isOpen_univ := (h i).1
        isOpen_inter := (h i).2.1
        isOpen_sUnion := (h i).2.2 }
    have hti : ∀ U : Lower, ti ≤ toTop U := by
      intro U s hs
      exact U.property.2 i hs
    have hle : ti ≤ t := ht.2 ti hti
    intro s hs
    exact hle s hs
  have hT'_greatest : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    intro T'' hT'' hT''sub
    let U : Lower := ⟨T'', hT'', hT''sub⟩
    have hle : t ≤ toTop U := ht.1 U
    intro s hs
    exact hle s hs
  refine ⟨T', ⟨hT'_top, hT'_sub, hT'_greatest⟩, ?_⟩
  intro T'' hT''
  apply Set.Subset.antisymm
  · exact hT'_greatest T'' hT''.1 hT''.2.1
  · exact hT''.2.2 T' hT'_top hT'_sub
