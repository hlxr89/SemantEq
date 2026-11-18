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
  letI : CompactSpace X1 := isCompact_iff_compactSpace.mp hX1.isCompact
  letI : CompactSpace X2 := isCompact_iff_compactSpace.mp hX2.isCompact
  letI : SecondCountableTopology X1 := inferInstance
  letI : SecondCountableTopology X2 := inferInstance

  let B1 := countableBasis X1
  let B2 := countableBasis X2
  choose E1 hE1o hE1 using fun b : B1 =>
    isOpen_induced_iff.mp ((isBasis_countableBasis X1).isOpen b.property)
  choose E2 hE2o hE2 using fun b : B2 =>
    isOpen_induced_iff.mp ((isBasis_countableBasis X2).isOpen b.property)

  let C1 : Set (Set X) := range E1 ∪ {X1ᶜ}
  let C2 : Set (Set X) := range E2 ∪ {X2ᶜ}
  let B : Set (Set X) := image2 (· ∩ ·) C1 C2

  have hC1c : C1.Countable :=
    (countable_range E1).union (countable_singleton X1ᶜ)
  have hC2c : C2.Countable :=
    (countable_range E2).union (countable_singleton X2ᶜ)
  have hBc : B.Countable := hC1c.image2 hC2c (· ∩ ·)

  have hC1o : ∀ s ∈ C1, IsOpen s := by
    rintro s (hs | hs)
    · rcases hs with ⟨b, rfl⟩
      exact hE1o b
    · simpa only [mem_singleton_iff] using hs ▸ hX1.isOpen_compl
  have hC2o : ∀ s ∈ C2, IsOpen s := by
    rintro s (hs | hs)
    · rcases hs with ⟨b, rfl⟩
      exact hE2o b
    · simpa only [mem_singleton_iff] using hs ▸ hX2.isOpen_compl

  have hBbasis : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨s1, hs1, s2, hs2, rfl⟩
      exact (hC1o s1 hs1).inter (hC2o s2 hs2)
    · intro a u hau huo
      have choose_side1 : ∃ s1 ∈ C1, a ∈ s1 ∧ ∀ y ∈ X1, y ∈ s1 → y ∈ u := by
        by_cases ha : a ∈ X1
        · let a1 : X1 := ⟨a, ha⟩
          obtain ⟨b, hbB, hab, hbu⟩ := (isBasis_countableBasis X1).exists_subset_of_mem_open
            (show a1 ∈ ((↑) : X1 → X) ⁻¹' u from hau) (huo.preimage continuous_subtype_val)
          let b1 : B1 := ⟨b, hbB⟩
          refine ⟨E1 b1, Or.inl ⟨b1, rfl⟩, ?_, ?_⟩
          · have : a1 ∈ ((↑) : X1 → X) ⁻¹' E1 b1 := by simpa [hE1 b1] using hab
            exact this
          · intro y hyX1 hys
            have hyb : (⟨y, hyX1⟩ : X1) ∈ b := by
              have : (⟨y, hyX1⟩ : X1) ∈ ((↑) : X1 → X) ⁻¹' E1 b1 := hys
              simpa [hE1 b1] using this
            exact hbu hyb
        · refine ⟨X1ᶜ, Or.inr (mem_singleton X1ᶜ), ha, ?_⟩
          intro y hyX1 hyc
          exact (hyc hyX1).elim
      have choose_side2 : ∃ s2 ∈ C2, a ∈ s2 ∧ ∀ y ∈ X2, y ∈ s2 → y ∈ u := by
        by_cases ha : a ∈ X2
        · let a2 : X2 := ⟨a, ha⟩
          obtain ⟨b, hbB, hab, hbu⟩ := (isBasis_countableBasis X2).exists_subset_of_mem_open
            (show a2 ∈ ((↑) : X2 → X) ⁻¹' u from hau) (huo.preimage continuous_subtype_val)
          let b2 : B2 := ⟨b, hbB⟩
          refine ⟨E2 b2, Or.inl ⟨b2, rfl⟩, ?_, ?_⟩
          · have : a2 ∈ ((↑) : X2 → X) ⁻¹' E2 b2 := by simpa [hE2 b2] using hab
            exact this
          · intro y hyX2 hys
            have hyb : (⟨y, hyX2⟩ : X2) ∈ b := by
              have : (⟨y, hyX2⟩ : X2) ∈ ((↑) : X2 → X) ⁻¹' E2 b2 := hys
              simpa [hE2 b2] using this
            exact hbu hyb
        · refine ⟨X2ᶜ, Or.inr (mem_singleton X2ᶜ), ha, ?_⟩
          intro y hyX2 hyc
          exact (hyc hyX2).elim
      obtain ⟨s1, hs1C, ha1, hs1u⟩ := choose_side1
      obtain ⟨s2, hs2C, ha2, hs2u⟩ := choose_side2
      refine ⟨s1 ∩ s2, ⟨s1, hs1C, s2, hs2C, rfl⟩, ⟨ha1, ha2⟩, ?_⟩
      intro y hy
      have hy12 : y ∈ X1 ∨ y ∈ X2 := by
        have : y ∈ X1 ∪ X2 := by simpa [hX]
        exact this
      exact hy12.elim (· |> fun hy1 => hs1u y hy1 hy.1) (· |> fun hy2 => hs2u y hy2 hy.2)

  letI : SecondCountableTopology X := hBbasis.secondCountableTopology hBc
  infer_instance
