import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem exercise_13_4b2_assumed (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X : Type*} (T : ι → TopologicalSpace X) : ∃! S : TopologicalSpace X, (∀ i, S ≤ T i) ∧ ∀ T' : TopologicalSpace X, (∀ i, T' ≤ T i) → T' ≤ S := by
  let A := {V : TopologicalSpace X //
    ∀ i s, @IsOpen X (T i) s → @IsOpen X V s}
  let O : A → Set (Set X) := fun V => {s | @IsOpen X V.1 s}
  have hO : ∀ V, is_topology X (O V) := by
    intro V
    letI : TopologicalSpace X := V.1
    exact ⟨isOpen_univ, fun s t hs ht => hs.inter ht,
      fun s hs => isOpen_sUnion (fun t ht => hs t ht)⟩
  obtain ⟨U, hU, huniq⟩ := exercise_13_4b2_assumed X A O hO
  let S : TopologicalSpace X :=
    { IsOpen := fun s => s ∈ U
      isOpen_univ := hU.1.1
      isOpen_inter := hU.1.2.1
      isOpen_sUnion := hU.1.2.2 }
  refine ⟨S, ?_, ?_⟩
  · constructor
    · intro i
      intro s hs
      exact hU.2.2 {s | @IsOpen X (T i) s}
        (by
          letI : TopologicalSpace X := T i
          exact ⟨isOpen_univ, fun a b ha hb => ha.inter hb,
            fun c hc => isOpen_sUnion (fun a ha => hc a ha)⟩)
        (fun V t ht => V.2 i t ht) hs
    · intro T' hT'
      let V : A := ⟨T', fun i s hs => hT' i s hs⟩
      exact fun s hs => hU.2.1 V hs
  · intro S' hS'
    apply TopologicalSpace.ext
    funext s
    apply propext
    constructor
    · intro hs
      exact hS'.2 S
        (fun i t ht => hU.2.2 {s | @IsOpen X (T i) s}
          (by
            letI : TopologicalSpace X := T i
            exact ⟨isOpen_univ, fun a b ha hb => ha.inter hb,
              fun c hc => isOpen_sUnion (fun a ha => hc a ha)⟩)
          (fun V u hu => V.2 i u hu) ht) s hs
    · intro hs
      let V : A := ⟨S', fun i t ht => hS'.1 i t ht⟩
      exact hU.2.1 V hs
