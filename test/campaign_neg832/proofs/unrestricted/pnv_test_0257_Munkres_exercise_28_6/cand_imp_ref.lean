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
  rcases dummy_assumed f hf.dist_eq with ⟨h_bijective, _, h_continuous⟩
  have h_homeomorph : IsHomeomorph f :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨h_continuous, h_bijective⟩
  exact ⟨h_continuous, h_bijective, h_homeomorph.isOpenMap⟩
