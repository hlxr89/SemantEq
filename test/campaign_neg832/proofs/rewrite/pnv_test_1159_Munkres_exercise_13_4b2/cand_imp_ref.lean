import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

def topologyOf {X : Type*} (T : Set (Set X)) (h : is_topology X T) : TopologicalSpace X where
  IsOpen s := s ∈ T
  isOpen_univ := h.1
  isOpen_inter s t := h.2.1 s t
  isOpen_sUnion s := h.2.2 s

def opensOf {X : Type*} (t : TopologicalSpace X) : Set (Set X) :=
  {s | @IsOpen X t s}

theorem opensOf_is_topology {X : Type*} (t : TopologicalSpace X) :
    is_topology X (opensOf t) :=
  ⟨t.isOpen_univ, t.isOpen_inter, t.isOpen_sUnion⟩

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u} (T : ι → TopologicalSpace X) : ∃ (t : TopologicalSpace X), ∀ (i : ι), t ≤ T i ∧ ∀ (t' : TopologicalSpace X), (∀ (i : ι), t' ≤ T i) → t' ≤ t := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let S : I → TopologicalSpace X := fun i => topologyOf (T i) (h i)
  let U := {t : TopologicalSpace X // ∀ i, S i ≤ t}
  obtain ⟨t, ht⟩ := dummy_assumed (fun s : U => s.1)
  let uTop : U := ⟨⊤, fun i => le_top⟩
  have htGreat : ∀ (t' : TopologicalSpace X), (∀ s : U, t' ≤ s.1) → t' ≤ t :=
    (ht uTop).2
  have htLower : ∀ s : U, t ≤ s.1 := fun s => (ht s).1
  have hTi : ∀ i, S i ≤ t := fun i => htGreat (S i) (fun s => s.2 i)
  refine ⟨opensOf t, ?_, ?_⟩
  · refine ⟨opensOf_is_topology t, ?_, ?_⟩
    · intro i V hV
      exact hTi i V hV
    · intro T'' hT'' hsub V hV
      let t'' := topologyOf T'' hT''
      have ht'' : ∀ i, S i ≤ t'' := by
        intro i _ hW
        exact hsub i hW
      exact htLower ⟨t'', ht''⟩ V hV
  · intro R hR
    apply Set.Subset.antisymm
    · exact htLower ⟨topologyOf R hR.1, fun i _ hV => hR.2.1 i hV⟩
    · exact hR.2.2 (opensOf t) (opensOf_is_topology t) hTi
