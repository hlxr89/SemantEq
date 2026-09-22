import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] [CompactSpace X] (f : X → X) (hf : ∀ x y : X, dist (f x) (f y) = dist x y) : Function.Bijective f ∧ ∃ h : Homeomorph X X, h.toFun = f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  obtain ⟨hbij, h, hh⟩ := dummy_assumed f hf.dist_eq
  refine ⟨?_, hbij, ?_⟩
  · rw [← hh]
    exact h.continuous
  · rw [← hh]
    exact h.isOpenMap
