import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {ι : Type*} {X : ι → Type*} [Π α, TopologicalSpace (X α)] (h : NormalSpace (Π α, X α)) (α : ι) [ne : Nonempty (X α)] : NormalSpace (X α) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  intro i
  letI : Nonempty (X i) := h i
  exact dummy_assumed h2 i
