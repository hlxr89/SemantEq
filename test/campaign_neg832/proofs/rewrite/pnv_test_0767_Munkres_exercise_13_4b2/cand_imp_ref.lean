import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! S : TopologicalSpace X, (∀ i, S ≤ T i) ∧ ∀ T' : TopologicalSpace X, (∀ i, T' ≤ T i) → T' ≤ S := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let TS : I → TopologicalSpace X := fun i =>
    { IsOpen := T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  let B := { U : TopologicalSpace X // ∀ i s, U.IsOpen s → s ∈ T i }
  obtain ⟨S, hS, hS_unique⟩ := dummy_assumed (fun U : B => U.1)
  refine ⟨S.IsOpen, ?_, ?_⟩
  · refine ⟨⟨S.isOpen_univ, S.isOpen_inter, S.isOpen_sUnion⟩, ?_, ?_⟩
    · intro i
      exact hS.2 (TS i) (fun U => U.2 i)
    intro T'' hT'' hsub
    let U : TopologicalSpace X :=
      { IsOpen := T''
        isOpen_univ := hT''.1
        isOpen_inter := hT''.2.1
        isOpen_sUnion := hT''.2.2 }
    exact hS.1 ⟨U, hsub⟩
  · intro O hO
    let U : TopologicalSpace X :=
      { IsOpen := O
        isOpen_univ := hO.1.1
        isOpen_inter := hO.1.2.1
        isOpen_sUnion := hO.1.2.2 }
    have hUS : U = S := by
      apply le_antisymm
      · exact hO.2.2 S.IsOpen ⟨S.isOpen_univ, S.isOpen_inter, S.isOpen_sUnion⟩
          (fun i => hS.2 (TS i) (fun V => V.2 i))
      · exact hS.1 ⟨U, hO.2.1⟩
    exact congrArg (fun V : TopologicalSpace X => V.IsOpen) hUS
