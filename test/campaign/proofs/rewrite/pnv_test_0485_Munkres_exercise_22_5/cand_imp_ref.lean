import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hf : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpen (p '' A) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_22_5 {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p)
  (A : Set X) (hA : IsOpen A) : IsOpenMap (p ∘ Subtype.val : A → Y) := by
  intro U hU
  have hval : IsOpen (Subtype.val '' U) := hA.isOpenMap_subtype_val U hU
  have h := dummy_assumed p hp (Subtype.val '' U) hval
  rw [Set.image_image] at h
  exact h
