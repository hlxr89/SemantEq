import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, dist (f x) (f y) = dist x y) : Function.Bijective f ∧ Isometry f ∧ Continuous f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  obtain ⟨hbij, hiso, hcont⟩ := dummy_assumed f hf.dist_eq
  refine ⟨hcont, hbij, ?_⟩
  let e : X ≃ᵢ X :=
    { toEquiv := Equiv.ofBijective f hbij
      isometry_toFun := hiso }
  simpa [e] using e.toHomeomorph.isOpenMap
