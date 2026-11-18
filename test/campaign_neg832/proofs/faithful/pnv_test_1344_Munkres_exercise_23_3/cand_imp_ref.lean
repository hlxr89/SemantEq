import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [ConnectedSpace X] {A : Set X} (hA : IsConnected A) {ι : Type*} {Ai : ι → Set X} (hAi : ∀ i, IsConnected (Ai i)) (hU : ∀ i, (Ai i ∩ A).Nonempty) : IsConnected (A ∪ ⋃ i, Ai i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_3 {X α : Type*} [TopologicalSpace X]
  {A : α → Set X}
  (hAa : ∀ a, IsConnected (A a))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ a, A₀ ∩ A a ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ a, A a)) := by
  obtain ⟨x, hx⟩ := hA.nonempty
  let C : Set X := connectedComponent x
  have hA_C : A₀ ⊆ C := by
    simpa [C] using hA.subset_connectedComponent hx
  have hAa_C : ∀ a, A a ⊆ C := by
    intro a
    obtain ⟨y, hy₀, hya⟩ := Set.nonempty_iff_ne_empty.mpr (h a)
    have hyC : y ∈ connectedComponent x := by
      exact hA_C hy₀
    have ha_y : A a ⊆ connectedComponent y :=
      (hAa a).subset_connectedComponent hya
    simpa [C, connectedComponent_eq hyC] using ha_y
  letI : ConnectedSpace C := Subtype.connectedSpace (by
    simpa [C] using (isConnected_connectedComponent :
      IsConnected (connectedComponent x)))
  have hA' : IsConnected (((↑) : C → X) ⁻¹' A₀) := by
    apply hA.preimage_of_isClosedMap Subtype.val_injective
      (by simpa [C] using isClosed_connectedComponent.isClosedMap_subtype_val)
    intro y hy
    exact ⟨⟨y, hA_C hy⟩, rfl⟩
  have hAa' : ∀ a, IsConnected (((↑) : C → X) ⁻¹' A a) := by
    intro a
    apply (hAa a).preimage_of_isClosedMap Subtype.val_injective
      (by simpa [C] using isClosed_connectedComponent.isClosedMap_subtype_val)
    intro y hy
    exact ⟨⟨y, hAa_C a hy⟩, rfl⟩
  have hU' : ∀ a, ((((↑) : C → X) ⁻¹' A a) ∩
      (((↑) : C → X) ⁻¹' A₀)).Nonempty := by
    intro a
    obtain ⟨y, hy₀, hya⟩ := Set.nonempty_iff_ne_empty.mpr (h a)
    exact ⟨⟨y, hAa_C a hya⟩, hya, hy₀⟩
  have hc := dummy_assumed (X := C) hA' hAa' hU'
  have himg := hc.image ((↑) : C → X) continuous_subtype_val.continuousOn
  simpa only [Set.image_union, Set.image_iUnion, Set.image_preimage_eq_inter_range,
    Subtype.range_val, inter_eq_left.mpr hA_C,
    inter_eq_left.mpr (hAa_C _)] using himg
