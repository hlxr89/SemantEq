import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] [CompactSpace X] [T2Space X] {X1 X2 : Set X} (hX1 : IsClosed X1) (hX2 : IsClosed X2) (h1 : MetrizableSpace X1) (h2 : MetrizableSpace X2) (hX : X1 ∪ X2 = Set.univ) : MetrizableSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_34_9
  (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (X1 X2 : Set X) (hX1 : IsClosed X1) (hX2 : IsClosed X2)
  (hX : X1 ∪ X2 = univ) (hX1m : MetrizableSpace X1)
  (hX2m : MetrizableSpace X2) : MetrizableSpace X := by
  letI : MetrizableSpace X1 := hX1m
  letI : MetrizableSpace X2 := hX2m
  letI : CompactSpace X1 := isCompact_iff_compactSpace.mp hX1.isCompact
  letI : CompactSpace X2 := isCompact_iff_compactSpace.mp hX2.isCompact
  letI : SecondCountableTopology X1 := inferInstance
  letI : SecondCountableTopology X2 := inferInstance

  let O1 : countableBasis X1 → Set X := fun b ↦
    Classical.choose (isOpen_induced_iff.mp ((isBasis_countableBasis X1).isOpen b.2))
  let O2 : countableBasis X2 → Set X := fun b ↦
    Classical.choose (isOpen_induced_iff.mp ((isBasis_countableBasis X2).isOpen b.2))
  have hO1_open (b : countableBasis X1) : IsOpen (O1 b) :=
    (Classical.choose_spec
      (isOpen_induced_iff.mp ((isBasis_countableBasis X1).isOpen b.2))).1
  have hO2_open (b : countableBasis X2) : IsOpen (O2 b) :=
    (Classical.choose_spec
      (isOpen_induced_iff.mp ((isBasis_countableBasis X2).isOpen b.2))).1
  have hO1_pre (b : countableBasis X1) :
      ((↑) : X1 → X) ⁻¹' O1 b = (b : Set X1) :=
    (Classical.choose_spec
      (isOpen_induced_iff.mp ((isBasis_countableBasis X1).isOpen b.2))).2
  have hO2_pre (b : countableBasis X2) :
      ((↑) : X2 → X) ⁻¹' O2 b = (b : Set X2) :=
    (Classical.choose_spec
      (isOpen_induced_iff.mp ((isBasis_countableBasis X2).isOpen b.2))).2

  let P1 : Option (countableBasis X1) → Set X
    | some b => O1 b
    | none => X1ᶜ
  let P2 : Option (countableBasis X2) → Set X
    | some b => O2 b
    | none => X2ᶜ
  let B : Set (Set X) := Set.range fun p :
      Option (countableBasis X1) × Option (countableBasis X2) ↦
    P1 p.1 ∩ P2 p.2

  have hP1_open (a : Option (countableBasis X1)) : IsOpen (P1 a) := by
    cases a with
    | none => exact hX1.isOpen_compl
    | some b => exact hO1_open b
  have hP2_open (a : Option (countableBasis X2)) : IsOpen (P2 a) := by
    cases a with
    | none => exact hX2.isOpen_compl
    | some b => exact hO2_open b

  have hB_basis : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro V ⟨p, rfl⟩
      exact (hP1_open p.1).inter (hP2_open p.2)
    · intro x U hxU hU
      have hx1 : ∃ a : Option (countableBasis X1),
          x ∈ P1 a ∧ ∀ y, y ∈ X1 → y ∈ P1 a → y ∈ U := by
        by_cases hx : x ∈ X1
        · have hpreopen : IsOpen (((↑) : X1 → X) ⁻¹' U) :=
            hU.preimage continuous_subtype_val
          obtain ⟨b, hbB, hxb, hbU⟩ := (isBasis_countableBasis X1).exists_subset_of_mem_open
            (a := ⟨x, hx⟩) (by exact hxU) hpreopen
          let b' : countableBasis X1 := ⟨b, hbB⟩
          refine ⟨some b', ?_, ?_⟩
          · change x ∈ O1 b'
            have : (⟨x, hx⟩ : X1) ∈ ((↑) : X1 → X) ⁻¹' O1 b' := by
              rw [hO1_pre b']
              exact hxb
            exact this
          · intro y hy1 hyP
            exact hbU (by
              have hyP' : (⟨y, hy1⟩ : X1) ∈
                  ((↑) : X1 → X) ⁻¹' O1 b' := hyP
              rw [hO1_pre b'] at hyP'
              exact hyP')
        · refine ⟨none, ?_, ?_⟩
          · simpa [P1] using hx
          · intro y hy1 hyP
            exact (hyP hy1).elim
      have hx2 : ∃ a : Option (countableBasis X2),
          x ∈ P2 a ∧ ∀ y, y ∈ X2 → y ∈ P2 a → y ∈ U := by
        by_cases hx : x ∈ X2
        · have hpreopen : IsOpen (((↑) : X2 → X) ⁻¹' U) :=
            hU.preimage continuous_subtype_val
          obtain ⟨b, hbB, hxb, hbU⟩ := (isBasis_countableBasis X2).exists_subset_of_mem_open
            (a := ⟨x, hx⟩) (by exact hxU) hpreopen
          let b' : countableBasis X2 := ⟨b, hbB⟩
          refine ⟨some b', ?_, ?_⟩
          · change x ∈ O2 b'
            have : (⟨x, hx⟩ : X2) ∈ ((↑) : X2 → X) ⁻¹' O2 b' := by
              rw [hO2_pre b']
              exact hxb
            exact this
          · intro y hy2 hyP
            exact hbU (by
              have hyP' : (⟨y, hy2⟩ : X2) ∈
                  ((↑) : X2 → X) ⁻¹' O2 b' := hyP
              rw [hO2_pre b'] at hyP'
              exact hyP')
        · refine ⟨none, ?_, ?_⟩
          · simpa [P2] using hx
          · intro y hy2 hyP
            exact (hyP hy2).elim
      obtain ⟨a, hxa, haU⟩ := hx1
      obtain ⟨b, hxb, hbU⟩ := hx2
      refine ⟨P1 a ∩ P2 b, ⟨(a, b), rfl⟩, ⟨hxa, hxb⟩, ?_⟩
      intro y hy
      have hycover : y ∈ X1 ∪ X2 := by rw [hX]; exact Set.mem_univ y
      rcases hycover with hy1 | hy2
      · exact haU y hy1 hy.1
      · exact hbU y hy2 hy.2

  have hB_countable : B.Countable := Set.countable_range _
  letI : SecondCountableTopology X := hB_basis.secondCountableTopology hB_countable
  infer_instance
