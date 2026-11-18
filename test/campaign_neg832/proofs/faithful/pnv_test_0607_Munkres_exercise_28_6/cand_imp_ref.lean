import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u} [MetricSpace X] (f : X → X) (hf : ∀ x y : X, dist (f x) (f y) = dist x y) (hX : CompactSpace X) : Function.Bijective f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  have hbij : Function.Bijective f := dummy_assumed f hf.dist_eq inferInstance
  let e : X ≃ᵢ X :=
    { toEquiv := Equiv.ofBijective f hbij
      isometry_toFun := hf }
  have hopen : IsOpenMap f := by
    change IsOpenMap e
    exact e.toHomeomorph.isOpenMap
  exact ⟨hf.continuous, hbij, hopen⟩
