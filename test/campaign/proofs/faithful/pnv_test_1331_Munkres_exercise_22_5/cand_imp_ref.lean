import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- The input preambles have no local definitions. These transparent aliases
-- provide a common universe for the universe-polymorphism bridge.
universe u₁ u₂

private abbrev CommonLiftLeft (X : Type u₁) (Y : Type u₂) :=
  ULift.{max u₁ u₂, u₁} X

private abbrev CommonLiftRight (X : Type u₁) (Y : Type u₂) :=
  ULift.{max u₁ u₂, u₂} Y

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (h : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpen (p '' A) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_22_5 {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) : IsOpenMap (p ∘ Subtype.val : A → Y) := by
  intro U hU
  rw [isOpen_induced_iff] at hU
  obtain ⟨V, hV, rfl⟩ := hU
  let eX : CommonLiftLeft X Y ≃ₜ X := Homeomorph.ulift
  let eY : CommonLiftRight X Y ≃ₜ Y := Homeomorph.ulift
  let q : CommonLiftLeft X Y → CommonLiftRight X Y := eY.symm ∘ p ∘ eX
  have hq : IsOpenMap q := eY.symm.isOpenMap.comp (hp.comp eX.isOpenMap)
  let S : Set (CommonLiftLeft X Y) := eX ⁻¹' (V ∩ A)
  have hS : IsOpen S := (hV.inter hA).preimage eX.continuous
  have hopen : IsOpen (q '' S) := dummy_assumed hq S hS
  have hopen' : IsOpen (eY '' (q '' S)) := eY.isOpenMap _ hopen
  rw [show (p ∘ Subtype.val : A → Y) '' (Subtype.val ⁻¹' V) =
      eY '' (q '' S) by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨q (eX.symm a), ⟨eX.symm a, ?_, rfl⟩, ?_⟩
      · simpa [S] using And.intro ha a.property
      · simp [q]
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      have hc' : eX c ∈ V ∩ A := by simpa [S] using hc
      refine ⟨⟨eX c, hc'.2⟩, hc'.1, ?_⟩
      simp [q]]
  exact hopen'
