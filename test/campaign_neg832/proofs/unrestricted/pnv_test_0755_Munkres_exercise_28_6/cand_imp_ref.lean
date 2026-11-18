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
  have himage : f '' U = (f '' Uᶜ)ᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [mem_compl_iff, mem_image]
      rintro ⟨x', hx', hxx'⟩
      have : x' = x := hbij.1 hxx'
      subst x'
      exact hx' hx
    · intro hy
      obtain ⟨x, rfl⟩ := hbij.2 y
      refine ⟨x, ?_, rfl⟩
      by_contra hx
      exact hy ⟨x, hx, rfl⟩
  rw [himage]
  exact (hf.continuous.isClosedMap Uᶜ hU.isClosed_compl).isOpen_compl
