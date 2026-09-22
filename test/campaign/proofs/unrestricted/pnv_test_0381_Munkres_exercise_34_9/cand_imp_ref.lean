import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {X₁ X₂ : Set X} (hX₁ : IsClosed X₁) (hX₂ : IsClosed X₂) (h : X = X₁ ∪ X₂) (h₁ : MetrizableSpace X₁) (h₂ : MetrizableSpace X₂) : MetrizableSpace X := by
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
  have secondCountable_of_compact_closed_surj
      (q : X1 ⊕ X2 → X) (hq : Continuous q) (hsurj : Function.Surjective q)
      (hclosed : IsClosedMap q) : SecondCountableTopology X := by
    classical
    let V : Finset (countableBasis (X1 ⊕ X2)) → Set X := fun s =>
      (q '' (⋃ b ∈ s, (b : Set (X1 ⊕ X2)))ᶜ)ᶜ
    have hVo : ∀ s, IsOpen (V s) := by
      intro s
      exact hclosed _ (isClosed_compl_iff.mpr <| isOpen_biUnion fun b _ =>
        isOpen_of_mem_countableBasis b.property) |>.isOpen_compl
    have hVb : IsTopologicalBasis (Set.range V) := by
      apply isTopologicalBasis_of_isOpen_of_nhds
      · rintro _ ⟨s, rfl⟩
        exact hVo s
      · intro x U hxU hU
        have hpre : IsOpen (q ⁻¹' U) := hU.preimage hq
        choose B hBbasis hyB hBU using fun y : q ⁻¹' {x} =>
          (isBasis_countableBasis (X1 ⊕ X2)).exists_subset_of_mem_open
            (show (y : X1 ⊕ X2) ∈ q ⁻¹' U by
              change q y ∈ U
              rw [show q y = x by
                have hyx : q y ∈ ({x} : Set X) := y.property
                simpa only [mem_singleton_iff] using hyx]
              exact hxU) hpre
        have hfiber : IsCompact (q ⁻¹' {x}) :=
          (isClosed_singleton.preimage hq).isCompact
        obtain ⟨s, hs⟩ := hfiber.elim_finite_subcover B
          (fun y => isOpen_of_mem_countableBasis (hBbasis y))
          (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyB ⟨y, hy⟩⟩)
        let t : Finset (countableBasis (X1 ⊕ X2)) := s.image fun y => ⟨B y, hBbasis y⟩
        refine ⟨V t, ⟨t, rfl⟩, ?_, ?_⟩
        · simp only [V, mem_compl_iff, mem_image]
          rintro ⟨y, hy, hqy⟩
          have hyfiber : y ∈ q ⁻¹' {x} := by simpa [hqy]
          have hycover := hs hyfiber
          simp only [mem_iUnion] at hycover
          obtain ⟨z, hzs, hyBz⟩ := hycover
          have hBt : (⟨B z, hBbasis z⟩ : countableBasis (X1 ⊕ X2)) ∈ t := by
            exact Finset.mem_image.mpr ⟨z, hzs, rfl⟩
          apply hy
          simp only [mem_iUnion]
          exact ⟨⟨B z, hBbasis z⟩, hBt, hyBz⟩
        · intro z hz
          by_contra hzU
          apply hz
          change z ∈ q '' (⋃ b ∈ t, (b : Set (X1 ⊕ X2)))ᶜ
          obtain ⟨y, rfl⟩ := hsurj z
          refine ⟨y, ?_, rfl⟩
          simp only [mem_compl_iff]
          intro hyUnion
          simp only [mem_iUnion] at hyUnion
          obtain ⟨b, hbt, hyb⟩ := hyUnion
          rcases Finset.mem_image.mp hbt with ⟨w, hws, hbw⟩
          subst b
          exact hzU (hBU w hyb)
    exact hVb.secondCountableTopology (Set.countable_range V)
  let q : X1 ⊕ X2 → X := Sum.elim Subtype.val Subtype.val
  have hq : Continuous q := continuous_subtype_val.sumElim continuous_subtype_val
  have hsurj : Function.Surjective q := by
    intro x
    have hx : x ∈ X1 ∪ X2 := by rw [hX]; exact mem_univ x
    rcases hx with hx | hx
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  letI : SecondCountableTopology X :=
    secondCountable_of_compact_closed_surj q hq hsurj hq.isClosedMap
  infer_instance
