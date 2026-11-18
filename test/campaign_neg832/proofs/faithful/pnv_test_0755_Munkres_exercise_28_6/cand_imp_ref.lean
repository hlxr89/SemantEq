import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → X} (hf : Isometry f) : Function.Bijective f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  have hbij : Function.Bijective f := dummy_assumed hf
  refine ⟨hf.continuous, hbij, ?_⟩
  intro U hU
  rw [← isClosed_compl_iff, ← Set.image_compl_eq hbij]
  exact hf.continuous.isClosedMap Uᶜ hU.isClosed_compl
