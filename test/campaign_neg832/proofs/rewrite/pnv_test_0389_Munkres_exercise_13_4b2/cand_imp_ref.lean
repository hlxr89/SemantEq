import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [TopologicalSpace X] {α : Type*} (Ta : α → TopologicalSpace X) : ∃! τ : TopologicalSpace X, (∀ (a : α), τ ≤ Ta a) ∧ ∀ τ' : TopologicalSpace X, (∀ (a : α), τ' ≤ Ta a) → τ ≤ τ' := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let Ti : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  letI : TopologicalSpace X := ⊥
  obtain ⟨τ, hτ, hτ_unique⟩ := dummy_assumed Ti
  have hτ_bot : τ = (⊥ : TopologicalSpace X) := by
    apply le_antisymm
    · exact hτ.2 ⊥ (fun _ => bot_le)
    · exact bot_le
  let T' : Set (Set X) := {s | @IsOpen X τ s ∧ ∀ i, s ∈ T i}
  have hT'_topology : is_topology X T' := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨τ.isOpen_univ, fun i => (h i).1⟩
    · intro s t hs ht
      exact ⟨τ.isOpen_inter s t hs.1 ht.1,
        fun i => (h i).2.1 s t (hs.2 i) (ht.2 i)⟩
    · intro s hs
      exact ⟨τ.isOpen_sUnion s (fun t ht => (hs t ht).1),
        fun i => (h i).2.2 s (fun t ht => (hs t ht).2 i)⟩
  have hT'_sub : ∀ i, T' ⊆ T i := by
    intro i s hs
    exact hs.2 i
  have hT'_max : ∀ T'', is_topology X T'' →
      (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    intro T'' hT'' hT''_sub s hs
    constructor
    · rw [hτ_bot]
      trivial
    · intro i
      exact hT''_sub i hs
  have hT' : is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
      ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' :=
    ⟨hT'_topology, hT'_sub, hT'_max⟩
  refine ⟨T', hT', ?_⟩
  intro T'' hT''
  apply Set.Subset.antisymm
  · exact hT'.2.2 T'' hT''.1 hT''.2.1
  · exact hT''.2.2 T' hT'.1 hT'.2.1
