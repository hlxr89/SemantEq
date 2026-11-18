import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u} [MetricSpace X] (f : X → X) (hf : ∀ x y : X, dist (f x) (f y) = dist x y) (hX : CompactSpace X) : Function.Bijective f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  have hbij : Function.Bijective f := dummy_assumed f hf.dist_eq inferInstance
  have hhomeo : IsHomeomorph f :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨hf.continuous, hbij⟩
  exact ⟨hhomeo.continuous, hbij, hhomeo.isOpenMap⟩
