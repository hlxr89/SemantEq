import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! T₀ : TopologicalSpace X, (∀ α, T₀ ≤ T α) ∧ ∀ T' : TopologicalSpace X, (∀ α, T' ≤ T α) → T' ≤ T₀ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let spaces : I → TopologicalSpace X := fun i =>
    { IsOpen := T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  let C := {S : TopologicalSpace X // ∀ i s, S.IsOpen s → (spaces i).IsOpen s}
  obtain ⟨T₀, hT₀, hT₀_unique⟩ := dummy_assumed (fun S : C => S.1)
  refine ⟨{s | T₀.IsOpen s}, ?_, ?_⟩
  · exact ⟨⟨T₀.isOpen_univ, fun s t hs ht => T₀.isOpen_inter s t hs ht,
      fun A hA => T₀.isOpen_sUnion A (fun s hs => hA s hs)⟩,
      (by
        intro i s hs
        change T₀.IsOpen s at hs
        change (spaces i).IsOpen s
        exact hT₀.2 (spaces i) (fun S u hu => S.2 i u hu) s hs),
      (by
        intro U hU hUi s hs
        let S : TopologicalSpace X :=
          { IsOpen := U
            isOpen_univ := hU.1
            isOpen_inter := hU.2.1
            isOpen_sUnion := hU.2.2 }
        change S.IsOpen s at hs
        let cS : C := ⟨S, fun i u hu => hUi i hu⟩
        exact hT₀.1 cS s hs)⟩
  · intro U hU
    have heq := hT₀_unique
      { IsOpen := U
        isOpen_univ := hU.1.1
        isOpen_inter := hU.1.2.1
        isOpen_sUnion := hU.1.2.2 }
      ⟨(by
        intro S s hs
        exact hU.2.2 {u | S.1.IsOpen u}
          ⟨S.1.isOpen_univ,
            fun u v hu hv => S.1.isOpen_inter u v hu hv,
            fun A hA => S.1.isOpen_sUnion A (fun u hu => hA u hu)⟩
          (fun i u hu => S.2 i u hu) hs),
        (by
          intro S hS s hs
          let cU : C := ⟨
            { IsOpen := U
              isOpen_univ := hU.1.1
              isOpen_inter := hU.1.2.1
              isOpen_sUnion := hU.1.2.2 },
            fun i u hu => hU.2.1 i hu⟩
          exact hS cU s hs)⟩
    exact congrArg (fun Z : TopologicalSpace X => Z.IsOpen) heq
