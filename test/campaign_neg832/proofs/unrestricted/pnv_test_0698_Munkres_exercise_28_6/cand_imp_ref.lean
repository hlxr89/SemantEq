import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, dist (f x) (f y) = dist x y) : Function.Bijective f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  have hbij : Function.Bijective f := dummy_assumed f hf.dist_eq
  let e : X ≃ X := Equiv.ofBijective f hbij
  let ie : X ≃ᵢ X := IsometryEquiv.mk e hf
  exact ⟨hf.continuous, hbij, ie.toHomeomorph.isOpenMap⟩
