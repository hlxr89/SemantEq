import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} {ι : Type*} (T : ι → Filter X) : ∃ (T' : Filter X), (∀ α : ι, T α ≤ T') ∧ ∀ (S : Filter X), (∀ α : ι, S ≤ T α) → S ≤ T' := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  classical
  obtain ⟨F, hF, hF_max⟩ := dummy_assumed (X := X) (ι := I) (fun _ => ⊥)
  have hbot : (⊥ : Filter X) ≤ F := hF_max ⊥ (fun _ => le_rfl)
  let Tcommon : Set (Set X) := {s | ∀ i, s ∈ T i}
  let T' : Set (Set X) := if (⊥ : Filter X) ≤ F then Tcommon else ∅
  have hT' : T' = Tcommon := by
    simp [T', hbot]
  have hT'_topology : is_topology X T' := by
    rw [hT']
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (h i).1
    · intro s t hs ht i
      exact (h i).2.1 s t (hs i) (ht i)
    · intro s hs i
      exact (h i).2.2 s (fun t ht => hs t ht i)
  have hT'_sub : ∀ i, T' ⊆ T i := by
    rw [hT']
    intro i s hs
    exact hs i
  refine ⟨T', ⟨hT'_topology, hT'_sub, ?_⟩, ?_⟩
  · intro T'' hT'' hT''_sub s hs
    rw [hT']
    intro i
    exact hT''_sub i hs
  · intro U hU
    apply Set.Subset.antisymm
    · intro s hs
      rw [hT']
      intro i
      exact hU.2.1 i hs
    · exact hU.2.2 T' hT'_topology hT'_sub
