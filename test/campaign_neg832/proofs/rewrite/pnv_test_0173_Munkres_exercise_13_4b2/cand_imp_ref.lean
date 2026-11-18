import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! T₀ : TopologicalSpace X, (∀ α, T₀ ≤ T α) ∧ (∀ T', (∀ α, T' ≤ T α) → T' ≤ T₀) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let Ts : I → TopologicalSpace X := fun i =>
    TopologicalSpace.mk (T i) (h i).1 (h i).2.1 (h i).2.2
  let C := {S : TopologicalSpace X // ∀ i, Ts i ≤ S}
  let Cs : C → TopologicalSpace X := fun S => S.1
  obtain ⟨T₀, hT₀, _⟩ := dummy_assumed Cs
  let O₀ : Set (Set X) := {s | @IsOpen X T₀ s}
  have hO₀ : is_topology X O₀ ∧ (∀ i, O₀ ⊆ T i) ∧
      ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ O₀ := by
    refine ⟨⟨@isOpen_univ X T₀,
      fun _ _ hs ht => @IsOpen.inter X T₀ _ _ hs ht,
      fun _ hs => @isOpen_sUnion X T₀ _ hs⟩, ?_, ?_⟩
    · intro i
      intro s hs
      have hlow : ∀ S : C, Ts i ≤ Cs S := fun S => S.2 i
      have hi := hT₀.2 (Ts i) hlow
      rw [TopologicalSpace.le_def] at hi
      exact hi s hs
    · intro T' htop hsub
      let S : TopologicalSpace X :=
        TopologicalSpace.mk T' htop.1 htop.2.1 htop.2.2
      have hS : ∀ i, Ts i ≤ S := by
        intro i
        rw [TopologicalSpace.le_def]
        intro s hs
        exact hsub i hs
      let Sc : C := ⟨S, hS⟩
      have hle := hT₀.1 Sc
      rw [TopologicalSpace.le_def] at hle
      intro s hs
      exact hle s hs
  refine ⟨O₀, hO₀, ?_⟩
  intro O' hO'
  apply Set.Subset.antisymm
  · exact hO₀.2.2 O' hO'.1 hO'.2.1
  · exact hO'.2.2 O₀ hO₀.1 hO₀.2.1
