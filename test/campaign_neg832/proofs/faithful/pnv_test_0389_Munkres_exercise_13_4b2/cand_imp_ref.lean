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
  let Ta : I → TopologicalSpace X := fun i =>
    TopologicalSpace.mk (fun s => s ∈ T i) (h i).1 (h i).2.1 (h i).2.2
  letI : TopologicalSpace X := ⊤
  obtain ⟨τ, hτ, _⟩ := dummy_assumed Ta
  let discrete : TopologicalSpace X :=
    TopologicalSpace.mk (fun _ => True) trivial (fun _ _ _ _ => trivial) (fun _ _ => trivial)
  have hτdiscrete : τ ≤ discrete := by
    apply hτ.2
    intro i
    rw [TopologicalSpace.le_def]
    intro _ _
    trivial
  have hDiscrete : ∀ s : Set X, @IsOpen X τ s := by
    intro s
    exact (TopologicalSpace.le_def.mp hτdiscrete) s trivial
  let T' : Set (Set X) := {s | @IsOpen X τ s ∧ ∀ i, s ∈ T i}
  have hT'top : is_topology X T' := by
    constructor
    · exact ⟨τ.isOpen_univ, fun i => (h i).1⟩
    constructor
    · intro s t hs ht
      exact ⟨τ.isOpen_inter s t hs.1 ht.1,
        fun i => (h i).2.1 s t (hs.2 i) (ht.2 i)⟩
    · intro s hs
      constructor
      · exact τ.isOpen_sUnion s (fun t ht => (hs t ht).1)
      · intro i
        exact (h i).2.2 s (fun t ht => (hs t ht).2 i)
  have hT'sub : ∀ i, T' ⊆ T i := by
    intro i s hs
    exact hs.2 i
  have hT'max : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    intro T'' _ hsub s hs
    exact ⟨hDiscrete s, fun i => hsub i hs⟩
  refine ⟨T', ⟨hT'top, hT'sub, hT'max⟩, ?_⟩
  intro T'' hT''
  apply Set.Subset.antisymm
  · exact hT'max T'' hT''.1 hT''.2.1
  · exact hT''.2.2 T' hT'top hT'sub
