import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)] (hX : NormalSpace (∀ i, π i)) (i : ι) [Nonempty (π i)] : NormalSpace (π i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  intro i
  letI : Nonempty (X i) := h i
  exact dummy_assumed (X := X i) (π := X) h2 i
