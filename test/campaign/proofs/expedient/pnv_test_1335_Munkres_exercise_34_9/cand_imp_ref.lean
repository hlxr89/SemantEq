import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {X1 X2 : Set X} (hX1 : IsClosed X1) (hX2 : IsClosed X2) (hX : X = X1 ∪ X2) (hX1_met : MetrizableSpace X1) (hX2_met : MetrizableSpace X2) : MetrizableSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_34_9
  (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (X1 X2 : Set X) (hX1 : IsClosed X1) (hX2 : IsClosed X2)
  (hX : X1 ∪ X2 = univ) (hX1m : MetrizableSpace X1)
  (hX2m : MetrizableSpace X2) : MetrizableSpace X := by
  letI : CompactSpace X1 := isCompact_iff_compactSpace.mp hX1.isCompact
  letI : CompactSpace X2 := isCompact_iff_compactSpace.mp hX2.isCompact
  letI : MetrizableSpace X1 := hX1m
  letI : MetrizableSpace X2 := hX2m
  letI : SecondCountableTopology X1 := inferInstance
  letI : SecondCountableTopology X2 := inferInstance
  let lift1 : (countableBasis X1) → Set X := fun U ↦
    Classical.choose ((isOpen_induced_iff).1
      ((isBasis_countableBasis X1).isOpen U.property))
  let lift2 : (countableBasis X2) → Set X := fun U ↦
    Classical.choose ((isOpen_induced_iff).1
      ((isBasis_countableBasis X2).isOpen U.property))
  have lift1_open (U : countableBasis X1) : IsOpen (lift1 U) :=
    (Classical.choose_spec ((isOpen_induced_iff).1
      ((isBasis_countableBasis X1).isOpen U.property))).1
  have lift2_open (U : countableBasis X2) : IsOpen (lift2 U) :=
    (Classical.choose_spec ((isOpen_induced_iff).1
      ((isBasis_countableBasis X2).isOpen U.property))).1
  have lift1_pre (U : countableBasis X1) :
      ((↑) : X1 → X) ⁻¹' lift1 U = U :=
    (Classical.choose_spec ((isOpen_induced_iff).1
      ((isBasis_countableBasis X1).isOpen U.property))).2
  have lift2_pre (U : countableBasis X2) :
      ((↑) : X2 → X) ⁻¹' lift2 U = U :=
    (Classical.choose_spec ((isOpen_induced_iff).1
      ((isBasis_countableBasis X2).isOpen U.property))).2
  let B1 : Set (Set X) := Set.range lift1 ∪ {X1ᶜ}
  let B2 : Set (Set X) := Set.range lift2 ∪ {X2ᶜ}
  let B : Set (Set X) := Set.image2 (· ∩ ·) B1 B2
  have B1_count : B1.Countable :=
    Set.countable_range lift1 |>.union (Set.countable_singleton _)
  have B2_count : B2.Countable :=
    Set.countable_range lift2 |>.union (Set.countable_singleton _)
  have B_count : B.Countable := B1_count.image2 B2_count (· ∩ ·)
  have B1_open : ∀ U ∈ B1, IsOpen U := by
    rintro U (⟨V, rfl⟩ | rfl)
    · exact lift1_open V
    · exact hX1.isOpen_compl
  have B2_open : ∀ U ∈ B2, IsOpen U := by
    rintro U (⟨V, rfl⟩ | rfl)
    · exact lift2_open V
    · exact hX2.isOpen_compl
  have choose1 (x : X) (O : Set X) (hx : x ∈ O) (hO : IsOpen O) :
      ∃ U ∈ B1, x ∈ U ∧ U ∩ X1 ⊆ O := by
    by_cases hx1 : x ∈ X1
    · obtain ⟨V, hV, hxV, hVO⟩ :=
        (isBasis_countableBasis X1).exists_subset_of_mem_open
          (a := ⟨x, hx1⟩) (u := ((↑) : X1 → X) ⁻¹' O) hx
          (hO.preimage continuous_subtype_val)
      let V' : countableBasis X1 := ⟨V, hV⟩
      refine ⟨lift1 V', Or.inl ⟨V', rfl⟩, ?_, ?_⟩
      · have : (⟨x, hx1⟩ : X1) ∈ ((↑) : X1 → X) ⁻¹' lift1 V' := by
          rw [lift1_pre]
          exact hxV
        exact this
      · rintro y ⟨hyU, hy1⟩
        have hyV : (⟨y, hy1⟩ : X1) ∈ V := by
          have : (⟨y, hy1⟩ : X1) ∈ ((↑) : X1 → X) ⁻¹' lift1 V' := hyU
          rwa [lift1_pre] at this
        exact hVO hyV
    · exact ⟨X1ᶜ, Or.inr rfl, hx1, by simp⟩
  have choose2 (x : X) (O : Set X) (hx : x ∈ O) (hO : IsOpen O) :
      ∃ U ∈ B2, x ∈ U ∧ U ∩ X2 ⊆ O := by
    by_cases hx2 : x ∈ X2
    · obtain ⟨V, hV, hxV, hVO⟩ :=
        (isBasis_countableBasis X2).exists_subset_of_mem_open
          (a := ⟨x, hx2⟩) (u := ((↑) : X2 → X) ⁻¹' O) hx
          (hO.preimage continuous_subtype_val)
      let V' : countableBasis X2 := ⟨V, hV⟩
      refine ⟨lift2 V', Or.inl ⟨V', rfl⟩, ?_, ?_⟩
      · have : (⟨x, hx2⟩ : X2) ∈ ((↑) : X2 → X) ⁻¹' lift2 V' := by
          rw [lift2_pre]
          exact hxV
        exact this
      · rintro y ⟨hyU, hy2⟩
        have hyV : (⟨y, hy2⟩ : X2) ∈ V := by
          have : (⟨y, hy2⟩ : X2) ∈ ((↑) : X2 → X) ⁻¹' lift2 V' := hyU
          rwa [lift2_pre] at this
        exact hVO hyV
    · exact ⟨X2ᶜ, Or.inr rfl, hx2, by simp⟩
  have B_basis : IsTopologicalBasis B := isTopologicalBasis_of_isOpen_of_nhds
    (by
      rintro U ⟨U1, hU1, U2, hU2, rfl⟩
      exact (B1_open U1 hU1).inter (B2_open U2 hU2))
    (by
      intro x O hx hO
      obtain ⟨U1, hU1, hxU1, hU1O⟩ := choose1 x O hx hO
      obtain ⟨U2, hU2, hxU2, hU2O⟩ := choose2 x O hx hO
      refine ⟨U1 ∩ U2, ⟨U1, hU1, U2, hU2, rfl⟩, ⟨hxU1, hxU2⟩, ?_⟩
      intro y hy
      have hy12 : y ∈ X1 ∨ y ∈ X2 := by
        have : y ∈ X1 ∪ X2 := by rw [hX]; trivial
        exact this
      exact hy12.elim (fun hy1 ↦ hU1O ⟨hy.1, hy1⟩)
        (fun hy2 ↦ hU2O ⟨hy.2, hy2⟩))
  letI : SecondCountableTopology X := B_basis.secondCountableTopology B_count
  infer_instance
