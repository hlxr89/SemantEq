import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (h : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpen (p '' A) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_22_5 {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) : IsOpenMap (p ∘ Subtype.val : A → Y) := by
  have hopen_image (B : Set X) (hB : IsOpen B) : IsOpen (p '' B) := by
    -- non-rewrite step: encode the differently sized universes in one sum type
    let q : X ⊕ Y → X ⊕ Y := Sum.elim (Sum.inr ∘ p) Sum.inr
    have hq : IsOpenMap q :=
      (isOpenMap_inr.comp hp).sumElim isOpenMap_inr
    have hB' : IsOpen ((Sum.inl : X → X ⊕ Y) '' B) :=
      (Topology.IsOpenEmbedding.inl (X := X) (Y := Y)).isOpen_iff_image_isOpen.mp hB
    have hopen' := dummy_assumed hq ((Sum.inl : X → X ⊕ Y) '' B) hB'
    have hopen'' : IsOpen ((Sum.inr : Y → X ⊕ Y) '' (p '' B)) := by
      simpa only [q, Set.image_image, Sum.elim_inl, Function.comp_apply] using hopen'
    exact (Topology.IsOpenEmbedding.inr (X := X) (Y := Y)).isOpen_iff_image_isOpen.mpr hopen''
  intro U hU
  have hU' : IsOpen (Subtype.val '' U) :=
    hA.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mp hU
  have hopen := hopen_image (Subtype.val '' U) hU'
  simpa only [Set.image_image] using hopen
