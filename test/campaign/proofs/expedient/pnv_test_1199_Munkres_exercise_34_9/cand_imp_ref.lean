import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {X1 X2 : Set X} (hX1 : IsClosed X1) (hX2 : IsClosed X2) (hX : X = X1 ∪ X2) (hX1m : MetrizableSpace X1) (hX2m : MetrizableSpace X2) : MetrizableSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_34_9
  (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (X1 X2 : Set X) (hX1 : IsClosed X1) (hX2 : IsClosed X2)
  (hX : X1 ∪ X2 = univ) (hX1m : MetrizableSpace X1)
  (hX2m : MetrizableSpace X2) : MetrizableSpace X := by
  classical
  letI : MetrizableSpace X1 := hX1m
  letI : MetrizableSpace X2 := hX2m
  letI : CompactSpace X1 := isCompact_iff_compactSpace.mp hX1.isCompact
  letI : CompactSpace X2 := isCompact_iff_compactSpace.mp hX2.isCompact
  let lift1 (U : Set X1) : Set X :=
    if hU : IsOpen U then (isOpen_induced_iff.mp hU).choose else ∅
  let lift2 (U : Set X2) : Set X :=
    if hU : IsOpen U then (isOpen_induced_iff.mp hU).choose else ∅
  have hlift1 (U : Set X1) (hU : IsOpen U) :
      IsOpen (lift1 U) ∧ ((↑) : X1 → X) ⁻¹' lift1 U = U := by
    simpa only [lift1, dif_pos hU] using (isOpen_induced_iff.mp hU).choose_spec
  have hlift2 (U : Set X2) (hU : IsOpen U) :
      IsOpen (lift2 U) ∧ ((↑) : X2 → X) ⁻¹' lift2 U = U := by
    simpa only [lift2, dif_pos hU] using (isOpen_induced_iff.mp hU).choose_spec
  let C1 : Set (Set X1) := insert ∅ (countableBasis X1)
  let C2 : Set (Set X2) := insert ∅ (countableBasis X2)
  have hC1 : C1.Countable := (Set.countable_singleton ∅).union (countable_countableBasis X1)
  have hC2 : C2.Countable := (Set.countable_singleton ∅).union (countable_countableBasis X2)
  have hopenC1 {U : Set X1} (hU : U ∈ C1) : IsOpen U := by
    rcases hU with (rfl | hU)
    · exact isOpen_empty
    · exact isOpen_of_mem_countableBasis hU
  have hopenC2 {U : Set X2} (hU : U ∈ C2) : IsOpen U := by
    rcases hU with (rfl | hU)
    · exact isOpen_empty
    · exact isOpen_of_mem_countableBasis hU
  let B : Set (Set X) := image2
    (fun U1 U2 ↦ (lift1 U1 ∪ X1ᶜ) ∩ (lift2 U2 ∪ X2ᶜ)) C1 C2
  have hBc : B.Countable := hC1.image2 hC2 _
  have hBo : ∀ U ∈ B, IsOpen U := by
    rintro U ⟨U1, hU1, U2, hU2, rfl⟩
    exact ((hlift1 U1 (hopenC1 hU1)).1.union hX1.isOpen_compl).inter
      ((hlift2 U2 (hopenC2 hU2)).1.union hX2.isOpen_compl)
  have hBb : IsTopologicalBasis B := isTopologicalBasis_of_isOpen_of_nhds hBo <| by
    intro x V hxV hVo
    have e1 : ∃ U1 ∈ C1, x ∈ lift1 U1 ∪ X1ᶜ ∧
        lift1 U1 ∪ X1ᶜ ⊆ V ∪ X1ᶜ := by
      by_cases hx1 : x ∈ X1
      · obtain ⟨U1, hU1, hxU1, hU1V⟩ := (isBasis_countableBasis X1).exists_subset_of_mem_open
          (a := ⟨x, hx1⟩) (u := ((↑) : X1 → X) ⁻¹' V) hxV
          (hVo.preimage continuous_subtype_val)
        refine ⟨U1, mem_insert_of_mem ∅ hU1, Or.inl ?_, ?_⟩
        · rw [← (hlift1 U1 (isOpen_of_mem_countableBasis hU1)).2] at hxU1
          exact hxU1
        · intro z hz
          rcases hz with hz | hz
          · by_cases hz1 : z ∈ X1
            · left
              have hzU : (⟨z, hz1⟩ : X1) ∈ U1 := by
                rw [← (hlift1 U1 (isOpen_of_mem_countableBasis hU1)).2]
                exact hz
              exact hU1V hzU
            · exact Or.inr hz1
          · exact Or.inr hz
      · refine ⟨∅, mem_insert ∅ _, Or.inr hx1, ?_⟩
        intro z hz
        rcases hz with hz | hz
        · by_cases hz1 : z ∈ X1
          · exfalso
            have : (⟨z, hz1⟩ : X1) ∈ (∅ : Set X1) := by
              rw [← (hlift1 ∅ isOpen_empty).2]
              exact hz
            exact this
          · exact Or.inr hz1
        · exact Or.inr hz
    have e2 : ∃ U2 ∈ C2, x ∈ lift2 U2 ∪ X2ᶜ ∧
        lift2 U2 ∪ X2ᶜ ⊆ V ∪ X2ᶜ := by
      by_cases hx2 : x ∈ X2
      · obtain ⟨U2, hU2, hxU2, hU2V⟩ := (isBasis_countableBasis X2).exists_subset_of_mem_open
          (a := ⟨x, hx2⟩) (u := ((↑) : X2 → X) ⁻¹' V) hxV
          (hVo.preimage continuous_subtype_val)
        refine ⟨U2, mem_insert_of_mem ∅ hU2, Or.inl ?_, ?_⟩
        · rw [← (hlift2 U2 (isOpen_of_mem_countableBasis hU2)).2] at hxU2
          exact hxU2
        · intro z hz
          rcases hz with hz | hz
          · by_cases hz2 : z ∈ X2
            · left
              have hzU : (⟨z, hz2⟩ : X2) ∈ U2 := by
                rw [← (hlift2 U2 (isOpen_of_mem_countableBasis hU2)).2]
                exact hz
              exact hU2V hzU
            · exact Or.inr hz2
          · exact Or.inr hz
      · refine ⟨∅, mem_insert ∅ _, Or.inr hx2, ?_⟩
        intro z hz
        rcases hz with hz | hz
        · by_cases hz2 : z ∈ X2
          · exfalso
            have : (⟨z, hz2⟩ : X2) ∈ (∅ : Set X2) := by
              rw [← (hlift2 ∅ isOpen_empty).2]
              exact hz
            exact this
          · exact Or.inr hz2
        · exact Or.inr hz
    obtain ⟨U1, hU1, hxU1, hU1V⟩ := e1
    obtain ⟨U2, hU2, hxU2, hU2V⟩ := e2
    refine ⟨(lift1 U1 ∪ X1ᶜ) ∩ (lift2 U2 ∪ X2ᶜ),
      ⟨U1, hU1, U2, hU2, rfl⟩, ⟨hxU1, hxU2⟩, ?_⟩
    intro z hz
    have hz1 := hU1V hz.1
    have hz2 := hU2V hz.2
    rcases hz1 with hzV | hz1
    · exact hzV
    rcases hz2 with hzV | hz2
    · exact hzV
    exfalso
    have hz12 : z ∈ X1 ∪ X2 := by rw [hX]; exact mem_univ z
    exact hz12.elim hz1 hz2
  letI : SecondCountableTopology X := hBb.secondCountableTopology hBc
  exact metrizableSpace_of_t3_secondCountable X
