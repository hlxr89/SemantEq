import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem exercise_13_4b2_assumed (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X : Type*} (T : ι → TopologicalSpace X) : ∃! T₀ : TopologicalSpace X, (∀ α, T₀ ≤ T α) ∧ ∀ T' : TopologicalSpace X, (∀ α, T' ≤ T α) → T' ≤ T₀ := by
  let J := {U : Set (Set X) //
    is_topology X U ∧ ∀ α, {s | (T α).IsOpen s} ⊆ U}
  obtain ⟨S, hS, hS_unique⟩ := exercise_13_4b2_assumed X J
    (fun U => U.1) (fun U => U.2.1)
  let K : Set (Set X) := {s | ∀ U : J, s ∈ U.1}
  have hK : is_topology X K := by
    refine ⟨?_, ?_, ?_⟩
    · intro U
      exact U.2.1.1
    · intro s t hs ht U
      exact U.2.1.2.1 s t (hs U) (ht U)
    · intro s hs U
      exact U.2.1.2.2 s (fun t ht => hs t ht U)
  have hKS : K ⊆ S := hS.2.2 K hK (fun U s hs => hs U)
  have hcommon : ∀ α, {s | (T α).IsOpen s} ⊆ S := by
    intro α s hs
    exact hKS (fun U => U.2.2 α hs)
  let T₀ : TopologicalSpace X :=
    { IsOpen := fun s => s ∈ S
      isOpen_univ := hS.1.1
      isOpen_inter := hS.1.2.1
      isOpen_sUnion := hS.1.2.2 }
  refine ⟨T₀, ?_, ?_⟩
  · constructor
    · intro α
      exact TopologicalSpace.le_def.mpr (hcommon α)
    · intro T' hT'
      apply TopologicalSpace.le_def.mpr
      exact hS.2.1
        ⟨{s | T'.IsOpen s},
          ⟨⟨T'.isOpen_univ, T'.isOpen_inter, T'.isOpen_sUnion⟩,
            fun α => TopologicalSpace.le_def.mp (hT' α)⟩⟩
  · intro T₁ hT₁
    apply le_antisymm
    · apply TopologicalSpace.le_def.mpr
      exact hS.2.1
        ⟨{s | T₁.IsOpen s},
          ⟨⟨T₁.isOpen_univ, T₁.isOpen_inter, T₁.isOpen_sUnion⟩,
            fun α => TopologicalSpace.le_def.mp (hT₁.1 α)⟩⟩
    · exact hT₁.2 T₀ (fun α => TopologicalSpace.le_def.mpr (hcommon α))
