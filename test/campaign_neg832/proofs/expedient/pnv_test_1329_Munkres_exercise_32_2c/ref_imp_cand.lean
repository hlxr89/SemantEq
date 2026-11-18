import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_32_2c_assumed
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X : Type*} {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)] [∀ i, CompactSpace (π i)] [∀ i, Nonempty (π i)] (h : NormalSpace (∀ i, π i)) : ∀ i, NormalSpace (π i) := by
  exact exercise_32_2c_assumed (fun _ ↦ inferInstance) h
