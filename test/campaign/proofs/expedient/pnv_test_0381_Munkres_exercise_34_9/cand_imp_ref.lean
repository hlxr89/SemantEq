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
  let e1 : Option (countableBasis X1) → Set X := fun u => u.elim ∅ fun v =>
    Classical.choose (isOpen_induced_iff.mp (isOpen_of_mem_countableBasis v.property))
  let e2 : Option (countableBasis X2) → Set X := fun u => u.elim ∅ fun v =>
    Classical.choose (isOpen_induced_iff.mp (isOpen_of_mem_countableBasis v.property))
  let E1 : Option (countableBasis X1) → Set X := fun u => e1 u ∪ X1ᶜ
  let E2 : Option (countableBasis X2) → Set X := fun u => e2 u ∪ X2ᶜ
  let b : Set (Set X) := Set.range fun p : Option (countableBasis X1) × Option (countableBasis X2) =>
    E1 p.1 ∩ E2 p.2
  have he1 (u : Option (countableBasis X1)) : IsOpen (e1 u) := by
    cases u with
    | none => exact isOpen_empty
    | some u => exact (Classical.choose_spec (isOpen_induced_iff.mp
        (isOpen_of_mem_countableBasis u.property))).1
  have he2 (u : Option (countableBasis X2)) : IsOpen (e2 u) := by
    cases u with
    | none => exact isOpen_empty
    | some u => exact (Classical.choose_spec (isOpen_induced_iff.mp
        (isOpen_of_mem_countableBasis u.property))).1
  have hmem1 (u : countableBasis X1) (x : X) (hx : x ∈ X1) :
      x ∈ E1 (some u) ↔ (⟨x, hx⟩ : X1) ∈ (u : Set X1) := by
    have he := (Classical.choose_spec (isOpen_induced_iff.mp
      (isOpen_of_mem_countableBasis u.property))).2
    simp only [E1, e1, Option.elim, mem_union, mem_compl_iff, hx, not_true_eq_false, or_false]
    exact Set.ext_iff.mp he ⟨x, hx⟩
  have hmem2 (u : countableBasis X2) (x : X) (hx : x ∈ X2) :
      x ∈ E2 (some u) ↔ (⟨x, hx⟩ : X2) ∈ (u : Set X2) := by
    have he := (Classical.choose_spec (isOpen_induced_iff.mp
      (isOpen_of_mem_countableBasis u.property))).2
    simp only [E2, e2, Option.elim, mem_union, mem_compl_iff, hx, not_true_eq_false, or_false]
    exact Set.ext_iff.mp he ⟨x, hx⟩
  have hb : IsTopologicalBasis b := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨p, rfl⟩
      exact (he1 p.1).union hX1.isOpen_compl |>.inter ((he2 p.2).union hX2.isOpen_compl)
    · intro x U hxU hU
      have hxcover : x ∈ X1 ∨ x ∈ X2 := by
        have : x ∈ X1 ∪ X2 := by simpa [hX] using (show x ∈ (univ : Set X) from trivial)
        exact this
      have choose1 : ∃ u : Option (countableBasis X1), x ∈ E1 u ∧ E1 u ⊆ U ∪ X1ᶜ := by
        by_cases hx1 : x ∈ X1
        · obtain ⟨u, hu, hxu, hus⟩ := (isBasis_countableBasis X1).isOpen_iff.mp
              (hU.preimage continuous_subtype_val) ⟨x, hx1⟩ (by exact hxU)
          refine ⟨some ⟨u, hu⟩, (hmem1 ⟨u, hu⟩ x hx1).2 hxu, ?_⟩
          intro y hy
          by_cases hy1 : y ∈ X1
          · left
            exact hus ((hmem1 ⟨u, hu⟩ y hy1).1 hy)
          · exact Or.inr hy1
        · exact ⟨none, by simp [E1, e1, hx1]⟩
      have choose2 : ∃ u : Option (countableBasis X2), x ∈ E2 u ∧ E2 u ⊆ U ∪ X2ᶜ := by
        by_cases hx2 : x ∈ X2
        · obtain ⟨u, hu, hxu, hus⟩ := (isBasis_countableBasis X2).isOpen_iff.mp
              (hU.preimage continuous_subtype_val) ⟨x, hx2⟩ (by exact hxU)
          refine ⟨some ⟨u, hu⟩, (hmem2 ⟨u, hu⟩ x hx2).2 hxu, ?_⟩
          intro y hy
          by_cases hy2 : y ∈ X2
          · left
            exact hus ((hmem2 ⟨u, hu⟩ y hy2).1 hy)
          · exact Or.inr hy2
        · exact ⟨none, by simp [E2, e2, hx2]⟩
      obtain ⟨u1, hxu1, hu1⟩ := choose1
      obtain ⟨u2, hxu2, hu2⟩ := choose2
      refine ⟨E1 u1 ∩ E2 u2, ⟨(u1, u2), rfl⟩, ⟨hxu1, hxu2⟩, ?_⟩
      intro y hy
      rcases (by simpa [hX] using (show y ∈ (univ : Set X) from trivial) : y ∈ X1 ∪ X2) with hy1 | hy2
      · exact (hu1 hy.1).resolve_right (by simpa using hy1)
      · exact (hu2 hy.2).resolve_right (by simpa using hy2)
  haveI : SecondCountableTopology X := hb.secondCountableTopology (by
    change (Set.range fun p : Option (countableBasis X1) × Option (countableBasis X2) =>
      E1 p.1 ∩ E2 p.2).Countable
    exact Set.countable_range _)
  infer_instance
