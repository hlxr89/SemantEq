import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, dist (f x) (f y) = dist x y) : Isometry f ∧ Function.Bijective f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  rcases dummy_assumed f hf.dist_eq with ⟨h_isometry, h_bijective⟩
  let e : X ≃ᵢ X :=
    { toEquiv := Equiv.ofBijective f h_bijective
      isometry_toFun := h_isometry }
  exact ⟨h_isometry.continuous, h_bijective, e.toHomeomorph.isOpenMap⟩
