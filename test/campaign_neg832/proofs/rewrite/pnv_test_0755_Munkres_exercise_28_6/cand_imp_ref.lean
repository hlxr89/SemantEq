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
  have hbij := dummy_assumed hf
  refine ⟨hf.continuous, hbij, ?_⟩
  intro s hs
  rw [← isClosed_compl_iff, ← image_compl_eq hbij]
  exact hf.continuous.isClosedMap sᶜ hs.isClosed_compl
