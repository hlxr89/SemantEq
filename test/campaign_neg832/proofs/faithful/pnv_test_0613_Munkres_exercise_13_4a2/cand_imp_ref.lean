import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (𝒯 : Set (TopologicalSpace X)) : (⋃ (𝒯 : Set (TopologicalSpace X)), 𝒯) ≠ { ⊤ } := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4a2 :
  ∃ (X I : Type*) (T : I → Set (Set X)),
  (∀ i, is_topology X (T i)) ∧ ¬  is_topology X (⋃ i : I, T i) := by
  let U : Set (TopologicalSpace Bool) := ⋃ (𝒯 : Set (TopologicalSpace Bool)), 𝒯
  have hU : U ≠ {⊤} := dummy_assumed (X := Bool) ∅
  have hτ : ∃ τ : TopologicalSpace Bool, τ ≠ ⊤ := by
    by_contra h
    push_neg at h
    apply hU
    ext τ
    constructor
    · intro _
      exact Set.mem_singleton_iff.mpr (h τ)
    · intro _
      simp only [U, Set.mem_iUnion]
      exact ⟨{τ}, Set.mem_singleton τ⟩
  rcases hτ with ⟨τ, hτ⟩
  let W := {σ : TopologicalSpace Bool // σ ≠ ⊤}
  let w : W := ⟨τ, hτ⟩
  refine ⟨ULift (Option (Option W)), ULift Bool, ?_⟩
  let X := ULift (Option (Option W))
  let a : X := ⟨none⟩
  let b : X := ⟨some none⟩
  let c : X := ⟨some (some w)⟩
  let Tp : X → Set (Set X) := fun p => {v | v = ∅ ∨ p ∈ v}
  have hTp : ∀ p, is_topology X (Tp p) := by
    intro p
    refine ⟨?_, ?_, ?_⟩
    · exact Or.inr (Set.mem_univ p)
    · intro u v hu hv
      rcases hu with (rfl | hu)
      · exact Or.inl (Set.empty_inter v)
      rcases hv with (rfl | hv)
      · exact Or.inl (Set.inter_empty u)
      · exact Or.inr ⟨hu, hv⟩
    · intro V hV
      by_cases h : ∃ v ∈ V, p ∈ v
      · rcases h with ⟨v, hvV, hpv⟩
        exact Or.inr (Set.mem_sUnion_of_mem hpv hvV)
      · left
        ext x
        simp only [Set.mem_sUnion, Set.mem_empty_iff_false, iff_false]
        rintro ⟨v, hvV, hxv⟩
        rcases hV v hvV with (rfl | hpv)
        · exact hxv
        · exact h ⟨v, hvV, hpv⟩
  let T : ULift Bool → Set (Set X) := fun i => if i.down then Tp b else Tp a
  refine ⟨T, ?_, ?_⟩
  · intro i
    rcases i with ⟨i⟩
    cases i
    · exact hTp a
    · exact hTp b
  · intro htop
    let A : Set X := {a, c}
    let B : Set X := {b, c}
    have hA : A ∈ ⋃ i : ULift Bool, T i := by
      apply Set.mem_iUnion.mpr
      refine ⟨⟨false⟩, ?_⟩
      exact Or.inr (by simp [A, a])
    have hB : B ∈ ⋃ i : ULift Bool, T i := by
      apply Set.mem_iUnion.mpr
      refine ⟨⟨true⟩, ?_⟩
      exact Or.inr (by simp [B, b])
    have hAB := htop.2.1 A B hA hB
    rcases Set.mem_iUnion.mp hAB with ⟨i, hi⟩
    rcases i with ⟨i⟩
    cases i
    · rcases hi with (hi | hi)
      · have : c ∈ A ∩ B := by simp [A, B]
        rw [hi] at this
        exact this
      · simp [A, B, a, b, c, X] at hi
    · rcases hi with (hi | hi)
      · have : c ∈ A ∩ B := by simp [A, B]
        rw [hi] at this
        exact this
      · simp [A, B, a, b, c, X] at hi
