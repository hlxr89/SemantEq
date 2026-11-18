import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MetrizableSpace X] (X₁ X₂ : Set X) (h₁ : IsClosed X₁) (h₂ : IsClosed X₂) (hX : X = X₁ ∪ X₂) : MetrizableSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_34_9
  (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (X1 X2 : Set X) (hX1 : IsClosed X1) (hX2 : IsClosed X2)
  (hX : X1 ∪ X2 = univ) (hX1m : MetrizableSpace X1)
  (hX2m : MetrizableSpace X2) : MetrizableSpace X := by
  letI : MetrizableSpace X1 := hX1m
  letI : MetrizableSpace X2 := hX2m
  haveI : CompactSpace X1 := isCompact_iff_compactSpace.mp hX1.isCompact
  haveI : CompactSpace X2 := isCompact_iff_compactSpace.mp hX2.isCompact
  haveI : SecondCountableTopology X1 := inferInstance
  haveI : SecondCountableTopology X2 := inferInstance
  classical
  let B1 : Set (Set X1) := insert ∅ (countableBasis X1)
  let B2 : Set (Set X2) := insert ∅ (countableBasis X2)
  let e1 : Set X1 → Set X := fun U =>
    if U = ∅ then X1ᶜ
    else if hU : IsOpen U then Classical.choose (isOpen_induced_iff.mp hU) else ∅
  let e2 : Set X2 → Set X := fun U =>
    if U = ∅ then X2ᶜ
    else if hU : IsOpen U then Classical.choose (isOpen_induced_iff.mp hU) else ∅
  have he1 (U : Set X1) (hU : IsOpen U) :
      IsOpen (e1 U) ∧ ((↑) : X1 → X) ⁻¹' e1 U = U := by
    by_cases h : U = ∅
    · subst U
      simp [e1, hX1.isOpen_compl]
    · simpa [e1, h, hU] using (Classical.choose_spec (isOpen_induced_iff.mp hU))
  have he2 (U : Set X2) (hU : IsOpen U) :
      IsOpen (e2 U) ∧ ((↑) : X2 → X) ⁻¹' e2 U = U := by
    by_cases h : U = ∅
    · subst U
      simp [e2, hX2.isOpen_compl]
    · simpa [e2, h, hU] using (Classical.choose_spec (isOpen_induced_iff.mp hU))
  have hB1o (U : Set X1) (hU : U ∈ B1) : IsOpen U := by
    rcases hU with (rfl | hU)
    · exact isOpen_empty
    · exact (isBasis_countableBasis X1).isOpen hU
  have hB2o (U : Set X2) (hU : U ∈ B2) : IsOpen U := by
    rcases hU with (rfl | hU)
    · exact isOpen_empty
    · exact (isBasis_countableBasis X2).isOpen hU
  let B : Set (Set X) := image2 (· ∩ ·) (e1 '' B1) (e2 '' B2)
  have hB : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨_, ⟨U, hUB, rfl⟩, _, ⟨V, hVB, rfl⟩, rfl⟩
      exact (he1 U (hB1o U hUB)).1.inter (he2 V (hB2o V hVB)).1
    · intro x u hxu hu
      have choose1 : ∃ U ∈ B1, x ∈ e1 U ∧ X1 ∩ e1 U ⊆ u := by
        by_cases hx : x ∈ X1
        · obtain ⟨U, hUB, hxU, hUu⟩ := (isBasis_countableBasis X1).exists_subset_of_mem_open
              (a := ⟨x, hx⟩) hxu (hu.preimage continuous_subtype_val)
          have hUB' : U ∈ B1 := Or.inr hUB
          refine ⟨U, hUB', ?_, ?_⟩
          · have : ⟨x, hx⟩ ∈ ((↑) : X1 → X) ⁻¹' e1 U := by
              rw [(he1 U (hB1o U hUB')).2]
              exact hxU
            exact this
          · intro y hy
            have hyU' : ⟨y, hy.1⟩ ∈ ((↑) : X1 → X) ⁻¹' e1 U := hy.2
            have hyU : ⟨y, hy.1⟩ ∈ U :=
              (congrArg (fun s => ⟨y, hy.1⟩ ∈ s) (he1 U (hB1o U hUB')).2).mp hyU'
            exact hUu hyU
        · refine ⟨∅, Or.inl rfl, ?_, ?_⟩
          · simp [e1, hx]
          · simp [e1]
      have choose2 : ∃ V ∈ B2, x ∈ e2 V ∧ X2 ∩ e2 V ⊆ u := by
        by_cases hx : x ∈ X2
        · obtain ⟨V, hVB, hxV, hVu⟩ := (isBasis_countableBasis X2).exists_subset_of_mem_open
              (a := ⟨x, hx⟩) hxu (hu.preimage continuous_subtype_val)
          have hVB' : V ∈ B2 := Or.inr hVB
          refine ⟨V, hVB', ?_, ?_⟩
          · have : ⟨x, hx⟩ ∈ ((↑) : X2 → X) ⁻¹' e2 V := by
              rw [(he2 V (hB2o V hVB')).2]
              exact hxV
            exact this
          · intro y hy
            have hyV' : ⟨y, hy.1⟩ ∈ ((↑) : X2 → X) ⁻¹' e2 V := hy.2
            have hyV : ⟨y, hy.1⟩ ∈ V :=
              (congrArg (fun s => ⟨y, hy.1⟩ ∈ s) (he2 V (hB2o V hVB')).2).mp hyV'
            exact hVu hyV
        · refine ⟨∅, Or.inl rfl, ?_, ?_⟩
          · simp [e2, hx]
          · simp [e2]
      obtain ⟨U, hUB, hxU, hUu⟩ := choose1
      obtain ⟨V, hVB, hxV, hVu⟩ := choose2
      refine ⟨e1 U ∩ e2 V, ⟨e1 U, ⟨U, hUB, rfl⟩, e2 V, ⟨V, hVB, rfl⟩, rfl⟩,
        ⟨hxU, hxV⟩, ?_⟩
      intro y hy
      have hy12 : y ∈ X1 ∨ y ∈ X2 := by
        have : y ∈ X1 ∪ X2 := by rw [hX]; trivial
        exact this
      exact hy12.elim (fun hy1 => hUu ⟨hy1, hy.1⟩) (fun hy2 => hVu ⟨hy2, hy.2⟩)
  have hBc : B.Countable := by
    exact (((countable_countableBasis X1).insert ∅).image e1).image2
      (((countable_countableBasis X2).insert ∅).image e2) (· ∩ ·)
  letI : SecondCountableTopology X := hB.secondCountableTopology hBc
  infer_instance
