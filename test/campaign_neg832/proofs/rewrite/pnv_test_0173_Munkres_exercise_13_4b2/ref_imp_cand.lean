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
theorem dummy {X : Type*} (T : ι → TopologicalSpace X) : ∃! T₀ : TopologicalSpace X, (∀ α, T₀ ≤ T α) ∧ (∀ T', (∀ α, T' ≤ T α) → T' ≤ T₀) := by
  let C := {S : TopologicalSpace X // ∀ α, S ≤ T α}
  let O : C → Set (Set X) := fun S => {s | @IsOpen X S.1 s}
  have hO : ∀ S, is_topology X (O S) := by
    intro S
    exact ⟨@isOpen_univ X S.1,
      fun _ _ hs ht => @IsOpen.inter X S.1 _ _ hs ht,
      fun _ hs => @isOpen_sUnion X S.1 _ hs⟩
  obtain ⟨O₀, hO₀, _⟩ := exercise_13_4b2_assumed X C O hO
  let T₀ : TopologicalSpace X :=
    TopologicalSpace.mk O₀ hO₀.1.1 hO₀.1.2.1 hO₀.1.2.2
  have hT₀ : (∀ α, T₀ ≤ T α) ∧ (∀ T', (∀ α, T' ≤ T α) → T' ≤ T₀) := by
    constructor
    · intro α
      rw [TopologicalSpace.le_def]
      intro s hs
      let K : Set (Set X) := {u | ∀ S : C, @IsOpen X S.1 u}
      have hK : is_topology X K := by
        exact ⟨fun S => @isOpen_univ X S.1,
          fun _ _ hu hv S => @IsOpen.inter X S.1 _ _ (hu S) (hv S),
          fun _ hu S => @isOpen_sUnion X S.1 _ (fun u hu' => hu u hu' S)⟩
      have hKsub : ∀ S, K ⊆ O S := by
        intro S u hu
        exact hu S
      have hsK : s ∈ K := by
        intro S
        have hle := S.2 α
        rw [TopologicalSpace.le_def] at hle
        exact hle s hs
      have hout := hO₀.2.2 K hK hKsub hsK
      dsimp only [T₀]
      exact hout
    · intro T' hT'
      rw [TopologicalSpace.le_def]
      intro s hs
      let S : C := ⟨T', hT'⟩
      dsimp only [T₀] at hs
      exact hO₀.2.1 S hs
  refine ⟨T₀, hT₀, ?_⟩
  intro T' hT'
  exact le_antisymm (hT₀.2 T' hT'.1) (hT'.2 T₀ hT₀.1)
