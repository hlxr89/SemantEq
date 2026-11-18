import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (X : Type u) (α : Type v) (Tα : α → TopologicalSpace X) : ∃! (T : TopologicalSpace X), ∀ (a : α), Tα a ≤ T := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let t : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  obtain ⟨t', ht', ht'_unique⟩ := dummy_assumed X I t
  let T' : Set (Set X) := {s | IsOpen[t'] s}
  have hT' : is_topology X T' :=
    ⟨isOpen_univ, fun _ _ => IsOpen.inter, fun _ => isOpen_sUnion⟩
  have hT'_sub : ∀ i, T' ⊆ T i := by
    intro i s hs
    exact ht' i s hs
  have hT'_max : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    intro T'' hT'' hT''_sub
    let t'' : TopologicalSpace X :=
      { IsOpen := fun s => s ∈ T''
        isOpen_univ := hT''.1
        isOpen_inter := hT''.2.1
        isOpen_sUnion := hT''.2.2 }
    have ht'' : ∀ i, t i ≤ t'' := by
      intro i s hs
      exact hT''_sub i hs
    have heq : t'' = t' := ht'_unique t'' ht''
    intro s hs
    change IsOpen[t'] s
    change IsOpen[t''] s at hs
    rw [heq] at hs
    exact hs
  refine ⟨T', ⟨hT', hT'_sub, hT'_max⟩, ?_⟩
  intro T'' hT''
  let t'' : TopologicalSpace X :=
    { IsOpen := fun s => s ∈ T''
      isOpen_univ := hT''.1.1
      isOpen_inter := hT''.1.2.1
      isOpen_sUnion := hT''.1.2.2 }
  have ht'' : ∀ i, t i ≤ t'' := by
    intro i s hs
    exact hT''.2.1 i hs
  have heq : t'' = t' := ht'_unique t'' ht''
  ext s
  change IsOpen[t''] s ↔ IsOpen[t'] s
  rw [heq]
