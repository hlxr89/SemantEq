import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! t : TopologicalSpace X, (∀ i, t ≤ T i) ∧ (∀ t', (∀ i, t' ≤ T i) → t' ≤ t) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let L := {u : TopologicalSpace X // ∀ i, {s | IsOpen[u] s} ⊆ T i}
  obtain ⟨t, ht, _⟩ := dummy_assumed (T := fun u : L => u.1)
  let A : Set (Set X) := {s | IsOpen[t] s}
  have hA_top : is_topology X A :=
    ⟨isOpen_univ, fun _ _ => IsOpen.inter, fun _ => isOpen_sUnion⟩
  have hA_lower : ∀ i, A ⊆ T i := by
    intro i
    let ti : TopologicalSpace X :=
      { IsOpen := fun s => s ∈ T i
        isOpen_univ := (h i).1
        isOpen_inter := (h i).2.1
        isOpen_sUnion := (h i).2.2 }
    have hti : ti ≤ t := ht.2 ti (fun u => by
      rw [TopologicalSpace.le_def]
      exact u.property i)
    rw [TopologicalSpace.le_def] at hti
    exact hti
  have hA_greatest : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ A := by
    intro T'' hT'' hT''lower
    let t'' : TopologicalSpace X :=
      { IsOpen := fun s => s ∈ T''
        isOpen_univ := hT''.1
        isOpen_inter := hT''.2.1
        isOpen_sUnion := hT''.2.2 }
    have htt := ht.1 ⟨t'', hT''lower⟩
    rw [TopologicalSpace.le_def] at htt
    exact htt
  refine ⟨A, ⟨hA_top, hA_lower, hA_greatest⟩, ?_⟩
  intro A' hA'
  apply Set.Subset.antisymm
  · exact hA_greatest A' hA'.1 hA'.2.1
  · exact hA'.2.2 A hA_top hA_lower
