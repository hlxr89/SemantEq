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
  let τ : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  let U := {t : TopologicalSpace X // ∀ i, τ i ≤ t}
  obtain ⟨τ₀, hτ₀, _⟩ := dummy_assumed (fun t : U => t.1)
  let S : Set (Set X) := {s | IsOpen[τ₀] s}
  have hS : is_topology X S ∧ (∀ i, S ⊆ T i) ∧
      ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ S := by
    refine ⟨⟨τ₀.isOpen_univ, τ₀.isOpen_inter, τ₀.isOpen_sUnion⟩, ?_, ?_⟩
    · intro i
      exact hτ₀.2 (τ i) (fun t => t.2 i)
    · intro T'' hT'' hsub
      let τ'' : TopologicalSpace X :=
        { IsOpen := fun s => s ∈ T''
          isOpen_univ := hT''.1
          isOpen_inter := hT''.2.1
          isOpen_sUnion := hT''.2.2 }
      have hupp : ∀ i, τ i ≤ τ'' := hsub
      exact hτ₀.1 ⟨τ'', hupp⟩
  refine ⟨S, hS, ?_⟩
  intro S' hS'
  apply Set.Subset.antisymm
  · exact hS.2.2 S' hS'.1 hS'.2.1
  · exact hS'.2.2 S hS.1 hS.2.1
