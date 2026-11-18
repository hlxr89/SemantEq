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
  let τ : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  let A := {V : TopologicalSpace X //
    ∀ i s, @IsOpen X V s → @IsOpen X (τ i) s}
  obtain ⟨S, hS, huniq⟩ := dummy_assumed (fun V : A => V.1)
  refine ⟨{s | @IsOpen X S s}, ?_, ?_⟩
  · exact ⟨⟨isOpen_univ, fun s t hs ht => hs.inter ht,
      fun s hs => isOpen_sUnion (fun t ht => hs t ht)⟩,
      fun i s hs => hS.2 (τ i) (fun V t ht => V.2 i t ht) s hs,
      fun T'' hT'' hsub s hs =>
        let V : A :=
          ⟨{ IsOpen := fun t => t ∈ T''
             isOpen_univ := hT''.1
             isOpen_inter := hT''.2.1
             isOpen_sUnion := hT''.2.2 },
           fun i t ht => hsub i ht⟩
        hS.1 V s hs⟩
  · intro U hU
    apply Set.ext
    intro s
    constructor
    · intro hs
      let V : A :=
        ⟨{ IsOpen := fun t => t ∈ U
           isOpen_univ := hU.1.1
           isOpen_inter := hU.1.2.1
           isOpen_sUnion := hU.1.2.2 },
         fun i t ht => hU.2.1 i ht⟩
      exact hS.1 V s hs
    · intro hs
      exact hU.2.2 {s | @IsOpen X S s}
        ⟨isOpen_univ, fun a b ha hb => ha.inter hb,
          fun c hc => isOpen_sUnion (fun a ha => hc a ha)⟩
        (fun i t ht => hS.2 (τ i) (fun V u hu => V.2 i u hu) t ht) hs
